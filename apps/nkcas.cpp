// apps/nkcas.cpp — standalone CLI over the numkit-cas core.
//
//   nkcas integrate "1/(x^3+2)" x
//   nkcas diff "x^2*sin(x)" x
//   nkcas print "1/2*x + 0.25"
//   nkcas            (reads "<command> <expr> <var>" lines from stdin)
//
// Exit codes: 0 success (proved / printed), 1 usage or parse error,
// 2 honest Unevaluated — corpus runs can count the difference.
//   nkcas corpus <file>   — §7 corpus run: id<TAB>var<TAB>expr lines,
//                           prints per-task outcomes and the summary
//                           (pass rate, verification rate, median/p95).
#include <keel/array.h>
#include <keel/core.h>
#include <keel/format.h>
#include <keel/fs.h>
#include <keel/string.h>
#include <numkit/cas/parse_expr.hpp>
#include <keel/cas/core/series.hpp>
#include <keel/cas/core/simplify.hpp>
#include <keel/cas/core/symsolve.hpp>
#include <keel/cas/integrate/ratint.hpp>
#include <keel/cas/ode/dsolve.hpp>
#include <keel/cas/poly/solve.hpp>
#include <keel/cas/rubi/rules.hpp>
#include <keel/cas/transform/fourier.hpp>
#include <keel/cas/transform/laplace.hpp>
#include <keel/cas/transform/ztrans.hpp>

#include "corpus_runner.hpp"

#include <cstdio>
#include <cstdlib>

namespace {

bool isSpace(char ch)
{
    return ch == ' ' || ch == '\t' || ch == '\r' || ch == '\n';
}

keel::StringRef trimRef(keel::StringRef s)
{
    keel::usize a = 0, b = s.size();
    while (a < b && isSpace(s[a]))
        ++a;
    while (b > a && isSpace(s[b - 1]))
        --b;
    return s.substr(a, b - a);
}

bool readStdinLine(keel::String &out)
{
    out.clear();
    char buf[1024];
    bool any = false;
    while (std::fgets(buf, sizeof(buf), stdin) != nullptr) {
        any = true;
        const keel::usize len = keel::StringRef(buf).size();
        if (len > 0 && buf[len - 1] == '\n') {
            out.append(keel::StringRef(buf, len - 1));
            if (!out.empty() && out.back() == '\r')
                out.pop_back();
            return true;
        }
        out.append(keel::StringRef(buf, len));
    }
    return any;
}

// Split "<command> <expr...> <var>" / "<command> <expr>": the variable
// is the last whitespace-separated token, the expression everything
// between (so expressions may contain spaces).
bool splitLine(keel::StringRef line, keel::String &cmd,
               keel::String &exprSrc, keel::String &var)
{
    keel::Array<keel::StringRef> words;
    keel::usize i = 0;
    while (i < line.size()) {
        while (i < line.size() && isSpace(line[i]))
            ++i;
        keel::usize start = i;
        while (i < line.size() && !isSpace(line[i]))
            ++i;
        if (i > start)
            words.push_back(line.substr(start, i - start));
    }
    if (words.empty())
        return false;
    cmd.assign(words.front());
    if (cmd == "print" || cmd == "expand" || cmd == "simplify") {
        exprSrc.assign(trimRef(line.substr(cmd.size())));
        return !exprSrc.empty();
    }
    if (cmd == "pade") {
        // "pade <expr...> <var> <x0> <m> <n>": last four tokens are var, x0, m, n.
        if (words.size() < 6)
            return false;
        const keel::StringRef nTok = words.back();
        const keel::StringRef mTok = words[words.size() - 2];
        const keel::StringRef x0Tok = words[words.size() - 3];
        const keel::StringRef varTok = words[words.size() - 4];
        const keel::usize nOff = line.rfind(nTok);
        const keel::usize mOff = line.substr(0, nOff).rfind(mTok);
        const keel::usize x0Off = line.substr(0, mOff).rfind(x0Tok);
        const keel::usize vOff = line.substr(0, x0Off).rfind(varTok);
        exprSrc.assign(trimRef(line.substr(cmd.size(), vOff - cmd.size())));
        var = keel::format("{}\t{}\t{}\t{}", varTok, x0Tok, mTok, nTok);
        return !exprSrc.empty();
    }
    if (cmd == "defint" || cmd == "symsum") {
        // "defint/symsum <expr...> <var> <a> <b>": last three tokens are var, a, b.
        if (words.size() < 5)
            return false;
        const keel::StringRef bTok = words.back();
        const keel::StringRef aTok = words[words.size() - 2];
        const keel::StringRef varTok = words[words.size() - 3];
        const keel::usize bOff = line.rfind(bTok);
        const keel::usize aOff = line.substr(0, bOff).rfind(aTok);
        const keel::usize vOff = line.substr(0, aOff).rfind(varTok);
        exprSrc.assign(trimRef(line.substr(cmd.size(), vOff - cmd.size())));
        var = keel::format("{}\t{}\t{}", varTok, aTok, bTok);
        return !exprSrc.empty();
    }
    if (cmd == "subs" || cmd == "eval" || cmd == "residue") {
        if ((cmd == "eval" || cmd == "residue") && words.size() == 2) {
            exprSrc.assign(trimRef(line.substr(cmd.size())));
            var.clear();
            return !exprSrc.empty();
        }
        // "subs <expr...> <from> <to>" / "eval <expr...> <var> <val>" /
        // "residue <expr...> <var> <z0>":
        // the last two tokens are the pair, everything between is the
        // expression.
        if (words.size() < 4)
            return false;
        const keel::StringRef to = words.back();
        const keel::StringRef from = words[words.size() - 2];
        const keel::usize toOff = line.rfind(to);
        const keel::usize fromOff = line.substr(0, toOff).rfind(from);
        exprSrc.assign(trimRef(line.substr(cmd.size(), fromOff - cmd.size())));
        var = keel::format("{}\t{}", from, to); // caller splits on the tab
        return !exprSrc.empty();
    }
    if (words.size() < 3)
        return false;
    var.assign(words.back());
    const keel::usize varOff = line.rfind(var);
    exprSrc.assign(trimRef(line.substr(cmd.size(), varOff - cmd.size())));
    return !exprSrc.empty();
}

int runSubs(keel::StringRef exprSrc, keel::StringRef fromSrc,
            keel::StringRef toSrc)
{
    keel::cas::Ctx ctx;
    keel::cas::Expr f, from, to;
    try {
        f = numkit::cas::parseExpr(ctx, exprSrc);
        from = numkit::cas::parseExpr(ctx, fromSrc);
        to = numkit::cas::parseExpr(ctx, toSrc);
    } catch (const numkit::cas::ParseError &e) {
        keel::println("parse error at offset {}: {}", e.pos(), e.what());
        return 1;
    }
    keel::println("{}", ctx.toString(ctx.subs(f, from, to)));
    return 0;
}

int runEval(keel::StringRef exprSrc, keel::StringRef varName,
            keel::StringRef valSrc)
{
    keel::cas::Ctx ctx;
    keel::cas::Expr f;
    try {
        f = numkit::cas::parseExpr(ctx, exprSrc);
    } catch (const numkit::cas::ParseError &e) {
        keel::println("parse error at offset {}: {}", e.pos(), e.what());
        return 1;
    }
    keel::Array<keel::Pair<keel::StringRef, double>> env;
    if (!varName.empty()) {
        keel::cas::Expr valExpr;
        try {
            valExpr = numkit::cas::parseExpr(ctx, valSrc);
        } catch (const numkit::cas::ParseError &e) {
            keel::println("parse error at offset {}: {}", e.pos(), e.what());
            return 1;
        }
        double valDbl = 0.0;
        if (!ctx.evalDouble(valExpr, {}, valDbl)) {
            keel::println("cannot evaluate point: {}", valSrc);
            return 1;
        }
        env.emplace_back(varName, valDbl);
    }
    double out = 0.0;
    if (!ctx.evalDouble(f, env, out)) {
        keel::println("Unevaluated (domain error, pole, or unresolved symbol)");
        return 2;
    }
    std::printf("%.16g\n", out);
    return 0;
}

int runTaylor(keel::StringRef exprSrc, keel::StringRef varName,
              keel::StringRef x0Src, int order)
{
    keel::cas::Ctx ctx;
    keel::cas::Expr f, x0;
    try {
        f = numkit::cas::parseExpr(ctx, exprSrc);
        x0 = x0Src.empty() ? ctx.zero() : numkit::cas::parseExpr(ctx, x0Src);
    } catch (const numkit::cas::ParseError &e) {
        keel::println("parse error at offset {}: {}", e.pos(), e.what());
        return 1;
    }
    const keel::cas::Expr var = ctx.symbol(varName);
    const keel::cas::Expr out = keel::cas::taylor(ctx, f, var, x0, order);
    if (out.isNull()) {
        keel::println("Unevaluated (pole, branch point, or beyond series domain)");
        return 2;
    }
    keel::println("{}", ctx.toString(out));
    return 0;
}

int runLimit(keel::StringRef exprSrc, keel::StringRef varName,
             keel::StringRef x0Src)
{
    keel::cas::Ctx ctx;
    keel::cas::Expr f, x0;
    try {
        f = numkit::cas::parseExpr(ctx, exprSrc);
        x0 = x0Src.empty() ? ctx.zero() : numkit::cas::parseExpr(ctx, x0Src);
    } catch (const numkit::cas::ParseError &e) {
        keel::println("parse error at offset {}: {}", e.pos(), e.what());
        return 1;
    }
    const keel::cas::Expr var = ctx.symbol(varName);
    const keel::cas::LimitResult r = keel::cas::limit(ctx, f, var, x0);
    if (r.proved()) {
        keel::println("{}", ctx.toString(r.value));
        return 0;
    }
    if (r.status == keel::cas::LimitResult::Status::Divergent) {
        keel::println("Divergent (pole of order {})", r.poleOrder);
        return 2;
    }
    keel::println("Unevaluated: {}", r.reason);
    return 2;
}

int runResidue(keel::StringRef exprSrc, keel::StringRef varName,
               keel::StringRef z0Src)
{
    keel::cas::Ctx ctx;
    keel::cas::Expr f, z0;
    try {
        f = numkit::cas::parseExpr(ctx, exprSrc);
        z0 = z0Src.empty() ? ctx.zero() : numkit::cas::parseExpr(ctx, z0Src);
    } catch (const numkit::cas::ParseError &e) {
        keel::println("parse error at offset {}: {}", e.pos(), e.what());
        return 1;
    }
    const keel::cas::Expr var = ctx.symbol(varName.empty() ? keel::StringRef("x") : varName);
    const keel::cas::Expr res = keel::cas::residue(ctx, f, var, z0);
    if (res.isNull()) {
        keel::println("Unevaluated (essential singularity, branch point, or beyond domain)");
        return 2;
    }
    keel::println("{}", ctx.toString(res));
    return 0;
}

int runDefInt(keel::StringRef exprSrc, keel::StringRef varName,
              keel::StringRef aSrc, keel::StringRef bSrc)
{
    keel::cas::Ctx ctx;
    keel::cas::Expr f, a, b;
    try {
        f = numkit::cas::parseExpr(ctx, exprSrc);
        a = numkit::cas::parseExpr(ctx, aSrc);
        b = numkit::cas::parseExpr(ctx, bSrc);
    } catch (const numkit::cas::ParseError &e) {
        keel::println("parse error at offset {}: {}", e.pos(), e.what());
        return 1;
    }
    const keel::cas::Expr var = ctx.symbol(varName);
    const keel::cas::DefiniteIntegral r =
        keel::cas::definiteIntegrate(ctx, f, var, a, b);
    if (r.proved()) {
        keel::println("{}", ctx.toString(r.value));
        keel::println("[certificate: PROVED_SYMBOLIC]");
        return 0;
    }
    if (r.status == keel::cas::DefiniteIntegral::Status::Divergent) {
        keel::println("Divergent: {}", r.reason);
        return 2;
    }
    keel::println("Unevaluated: {}", r.reason);
    return 2;
}

int runSymSum(keel::StringRef exprSrc, keel::StringRef varName,
              keel::StringRef aSrc, keel::StringRef bSrc)
{
    keel::cas::Ctx ctx;
    keel::cas::Expr f, a, b;
    try {
        f = numkit::cas::parseExpr(ctx, exprSrc);
        a = numkit::cas::parseExpr(ctx, aSrc);
        b = numkit::cas::parseExpr(ctx, bSrc);
    } catch (const numkit::cas::ParseError &e) {
        keel::println("parse error at offset {}: {}", e.pos(), e.what());
        return 1;
    }
    const keel::cas::Expr var = ctx.symbol(varName);
    const keel::cas::SymSumResult r =
        keel::cas::symsum(ctx, f, var, a, b);
    if (r.proved()) {
        keel::println("{}", ctx.toString(r.value));
        keel::println("[certificate: PROVED_SYMBOLIC]");
        return 0;
    }
    if (r.status == keel::cas::SymSumResult::Status::Divergent) {
        keel::println("Divergent: {}", r.reason);
        return 2;
    }
    keel::println("Unevaluated: {}", r.reason);
    return 2;
}

int runPade(keel::StringRef exprSrc, keel::StringRef varName,
            keel::StringRef x0Src, int m, int n)
{
    keel::cas::Ctx ctx;
    keel::cas::Expr f, x0;
    try {
        f = numkit::cas::parseExpr(ctx, exprSrc);
        x0 = x0Src.empty() ? ctx.zero() : numkit::cas::parseExpr(ctx, x0Src);
    } catch (const numkit::cas::ParseError &e) {
        keel::println("parse error at offset {}: {}", e.pos(), e.what());
        return 1;
    }
    const keel::cas::Expr var = ctx.symbol(varName);
    const keel::cas::PadeResult r =
        keel::cas::pade(ctx, f, var, x0, m, n);
    if (r.proved()) {
        keel::println("{}", ctx.toString(r.value));
        keel::println("[certificate: PROVED_SYMBOLIC]");
        return 0;
    }
    keel::println("Unevaluated: {}", r.reason);
    return 2;
}

int runLaplace(keel::StringRef exprSrc, keel::StringRef inVarName,
               keel::StringRef outVarName, bool inverse)
{
    keel::cas::Ctx ctx;
    keel::cas::Expr f;
    try {
        f = numkit::cas::parseExpr(ctx, exprSrc);
    } catch (const numkit::cas::ParseError &e) {
        keel::println("parse error at offset {}: {}", e.pos(), e.what());
        return 1;
    }
    const keel::cas::Expr vIn = ctx.symbol(inVarName);
    const keel::cas::Expr vOut = ctx.symbol(outVarName);
    const keel::cas::LaplaceResult r =
        inverse ? keel::cas::ilaplace(ctx, f, vIn, vOut)
                : keel::cas::laplace(ctx, f, vIn, vOut);
    if (r.proved()) {
        keel::println("{}", ctx.toString(r.F));
        keel::println("[certificate: PROVED_SYMBOLIC]");
        return 0;
    }
    keel::println("Unevaluated: {}", r.reason);
    return 2;
}

int runZTrans(keel::StringRef exprSrc, keel::StringRef inVarName,
              keel::StringRef outVarName, bool inverse)
{
    keel::cas::Ctx ctx;
    keel::cas::Expr f;
    try {
        f = numkit::cas::parseExpr(ctx, exprSrc);
    } catch (const numkit::cas::ParseError &e) {
        keel::println("parse error at offset {}: {}", e.pos(), e.what());
        return 1;
    }
    const keel::cas::Expr vIn = ctx.symbol(inVarName);
    const keel::cas::Expr vOut = ctx.symbol(outVarName);
    const keel::cas::ZTransResult r =
        inverse ? keel::cas::iztrans(ctx, f, vIn, vOut)
                : keel::cas::ztrans(ctx, f, vIn, vOut);
    if (r.proved()) {
        keel::println("{}", ctx.toString(r.F));
        keel::println("[certificate: PROVED_SYMBOLIC]");
        return 0;
    }
    keel::println("Unevaluated: {}", r.reason);
    return 2;
}

int runFourier(keel::StringRef exprSrc, keel::StringRef inVarName,
               keel::StringRef outVarName, bool inverse)
{
    keel::cas::Ctx ctx;
    keel::cas::Expr f;
    try {
        f = numkit::cas::parseExpr(ctx, exprSrc);
    } catch (const numkit::cas::ParseError &e) {
        keel::println("parse error at offset {}: {}", e.pos(), e.what());
        return 1;
    }
    const keel::cas::Expr vIn = ctx.symbol(inVarName);
    const keel::cas::Expr vOut = ctx.symbol(outVarName);
    const keel::cas::FourierResult r =
        inverse ? keel::cas::ifourier(ctx, f, vIn, vOut)
                : keel::cas::fourier(ctx, f, vIn, vOut);
    if (r.proved()) {
        keel::println("{}", ctx.toString(r.F));
        keel::println("[certificate: PROVED_SYMBOLIC]");
        return 0;
    }
    keel::println("Unevaluated: {}", r.reason);
    return 2;
}

int runCommand(keel::StringRef cmd, keel::StringRef exprSrc,
               keel::StringRef varName)
{
    if (cmd == "pade") {
        const keel::usize t1 = varName.find('\t');
        const keel::usize t2 = varName.find('\t', t1 + 1);
        const keel::usize t3 = varName.find('\t', t2 + 1);
        const keel::String mStr = keel::String::from(varName.substr(t2 + 1, t3 - t2 - 1));
        const keel::String nStr = keel::String::from(varName.substr(t3 + 1));
        return runPade(exprSrc, varName.substr(0, t1),
                       varName.substr(t1 + 1, t2 - t1 - 1),
                       std::atoi(mStr.c_str()),
                       std::atoi(nStr.c_str()));
    }
    if (cmd == "defint" || cmd == "symsum") {
        const keel::usize t1 = varName.find('\t');
        const keel::usize t2 = varName.find('\t', t1 + 1);
        if (cmd == "symsum") {
            return runSymSum(exprSrc, varName.substr(0, t1),
                             varName.substr(t1 + 1, t2 - t1 - 1),
                             varName.substr(t2 + 1));
        }
        return runDefInt(exprSrc, varName.substr(0, t1),
                         varName.substr(t1 + 1, t2 - t1 - 1),
                         varName.substr(t2 + 1));
    }
    if (cmd == "subs") {
        // splitLine packed "from\tto" into varName
        const keel::usize tab = varName.find('\t');
        return runSubs(exprSrc, varName.substr(0, tab), varName.substr(tab + 1));
    }
    if (cmd == "eval") {
        if (varName.empty())
            return runEval(exprSrc, "", "");
        const keel::usize tab = varName.find('\t');
        return runEval(exprSrc, varName.substr(0, tab), varName.substr(tab + 1));
    }
    if (cmd == "residue") {
        if (varName.empty())
            return runResidue(exprSrc, "x", "0");
        const keel::usize tab = varName.find('\t');
        if (tab == keel::kInvalidIndex)
            return runResidue(exprSrc, varName, "0");
        return runResidue(exprSrc, varName.substr(0, tab), varName.substr(tab + 1));
    }
    keel::cas::Ctx ctx;
    keel::cas::Expr f;
    try {
        f = numkit::cas::parseExpr(ctx, exprSrc);
    } catch (const numkit::cas::ParseError &e) {
        keel::println("parse error at offset {}: {}", e.pos(), e.what());
        return 1;
    }
    if (cmd == "print") {
        keel::println("{}", ctx.toString(f));
        return 0;
    }
    if (cmd == "expand") {
        keel::println("{}", ctx.toString(ctx.expand(f)));
        return 0;
    }
    if (cmd == "simplify") {
        keel::println("{}", ctx.toString(ctx.simplify(f)));
        return 0;
    }
    const keel::cas::Expr var = ctx.symbol(varName);
    if (cmd == "diff") {
        keel::println("{}", ctx.toString(ctx.diff(f, var)));
        return 0;
    }
    if (cmd == "taylor")
        return runTaylor(exprSrc, varName, "", 6);
    if (cmd == "limit")
        return runLimit(exprSrc, varName, "");
    if (cmd == "laplace")
        return runLaplace(exprSrc, varName.empty() ? keel::StringRef("t") : varName, "s", false);
    if (cmd == "ilaplace")
        return runLaplace(exprSrc, varName.empty() ? keel::StringRef("s") : varName, "t", true);
    if (cmd == "ztrans")
        return runZTrans(exprSrc, varName.empty() ? keel::StringRef("n") : varName, "z", false);
    if (cmd == "iztrans")
        return runZTrans(exprSrc, varName.empty() ? keel::StringRef("z") : varName, "n", true);
    if (cmd == "fourier")
        return runFourier(exprSrc, varName.empty() ? keel::StringRef("t") : varName, "w", false);
    if (cmd == "ifourier")
        return runFourier(exprSrc, varName.empty() ? keel::StringRef("w") : varName, "t", true);
    if (cmd == "integrate") {
        const keel::cas::RationalIntegral r =
            keel::cas::integrate(ctx, f, var);
        if (r.proved()) {
            keel::println("{}", ctx.toString(r.F));
            keel::println("[certificate: PROVED_SYMBOLIC]");
            return 0;
        }
        keel::println("Unevaluated: {}", r.reason);
        return 2;
    }
    if (cmd == "solve") {
        keel::cas::UPoly N, D;
        if (!keel::cas::toRational(ctx, f, var, N, D) || !D.isConst()) {
            keel::println("not a polynomial in {}", varName);
            return 1;
        }
        if (N.isZero()) {
            keel::println("every point (zero polynomial)");
            return 0;
        }
        const auto roots = keel::cas::solveRealRoots(N);
        if (roots.empty())
            keel::println("no real roots");
        for (const auto &s : roots) {
            if (s.isRational) {
                keel::println("root #{} = {}", s.realIndex, s.value.toString());
            } else {
                keel::println("root #{} in ({}, {}]", s.realIndex,
                              s.interval.lo.toString(),
                              s.interval.hi.toString());
            }
        }
        return 0;
    }
    if (cmd == "symsolve") {
        const auto roots = keel::cas::solveSymbolic(ctx, f, var);
        if (roots.empty()) {
            keel::println("no symbolic solutions found");
            return 2;
        }
        for (const auto &r : roots)
            keel::println("{}", ctx.toString(r));
        return 0;
    }
    if (cmd == "dsolve") {
        const keel::cas::Expr y = ctx.symbol("y");
        const keel::cas::OdeResult sol =
            keel::cas::dsolve1(ctx, f, var, y);
        if (sol.proved()) {
            keel::println("{}", ctx.toString(sol.y));
            keel::println("[certificate: PROVED_SYMBOLIC]");
            return 0;
        }
        keel::println("Unevaluated: {}", sol.reason);
        return 2;
    }
    if (cmd == "factor") {
        keel::cas::Expr factored;
        if (!keel::cas::factorExpr(ctx, f, var, factored)) {
            keel::println("not a rational function of {}", varName);
            return 1;
        }
        keel::println("{}", ctx.toString(factored));
        return 0;
    }
    if (cmd == "rubi") {
        // Apply the first matching Rubi rule of the committed slice,
        // certified by the Tier-1 gate (dF/dx == integrand).
        const keel::cas::Expr F =
            keel::cas::rubi::rubiApply(keel::cas::rubi::sliceTables(),
                                         ctx, f, var);
        if (F.isNull()) {
            keel::println("no certified rule application");
            return 2;
        }
        keel::println("{}", ctx.toString(F));
        keel::println("[certificate: PROVED_SYMBOLIC]");
        return 0;
    }
    keel::println("unknown command '{}' (integrate, diff, subs, print)", cmd);
    return 1;
}

const char *statusName(nkcorpus::TaskStatus s)
{
    switch (s) {
    case nkcorpus::TaskStatus::Proved: return "PROVED";
    case nkcorpus::TaskStatus::Unevaluated: return "UNEVALUATED";
    case nkcorpus::TaskStatus::ParseError: return "PARSE_ERROR";
    case nkcorpus::TaskStatus::MalformedLine: return "MALFORMED_LINE";
    }
    return "?";
}

int runCorpusFile(const char *path)
{
    auto fileRes = keel::fs_read_text(path);
    if (!fileRes) {
        keel::println("cannot open corpus file: {}", path);
        return 1;
    }
    const keel::String content = keel::move(fileRes).value();
    keel::Array<nkcorpus::CorpusTask> tasks;
    keel::usize lineNo = 0, malformed = 0;
    keel::StringRef rem = content.as_ref();
    while (!rem.empty()) {
        const keel::usize nl = rem.find('\n');
        keel::StringRef line = (nl == keel::kInvalidIndex) ? rem : rem.substr(0, nl);
        if (!line.empty() && line.back() == '\r')
            line.remove_suffix(1);
        ++lineNo;
        nkcorpus::CorpusTask t;
        if (nkcorpus::parseCorpusLine(line, t)) {
            tasks.push_back(keel::move(t));
        } else if (nkcorpus::lineKind(line) == nkcorpus::LineKind::Malformed) {
            ++malformed;
            keel::println("line {}\tMALFORMED_LINE", lineNo);
        }
        if (nl == keel::kInvalidIndex)
            break;
        rem.remove_prefix(nl + 1);
    }
    keel::Array<nkcorpus::TaskOutcome> outcomes;
    const nkcorpus::CorpusReport rep =
        nkcorpus::runCorpus(tasks, &outcomes);
    for (const nkcorpus::TaskOutcome &o : outcomes) {
        if (o.status != nkcorpus::TaskStatus::Proved && !o.detail.empty()) {
            keel::println("{}\t{}\t{}us\t{}nodes\t{}", o.id,
                          statusName(o.status), o.micros, o.answerNodes,
                          o.detail);
        } else {
            keel::println("{}\t{}\t{}us\t{}nodes", o.id,
                          statusName(o.status), o.micros, o.answerNodes);
        }
    }
    keel::println("----");
    keel::println("tasks: {} (+{} malformed lines)", rep.total, malformed);
    keel::println("proved: {} ({}%)", rep.proved, rep.passRatePct());
    keel::println("unevaluated: {}, parse errors: {}", rep.unevaluated,
                  rep.parseErrors);
    keel::println("verification rate: {}% of integrable",
                  rep.verificationRatePct());
    keel::println("median time: {}us, p95: {}us", rep.medianMicros,
                  rep.p95Micros);
    if (rep.withReference > 0) {
        keel::println("mean leaf ratio: {} (over {} referenced tasks)",
                      rep.meanLeafRatio, rep.withReference);
    }
    return 0;
}

void usage()
{
    keel::println("usage: nkcas <command> <expr> <var>\n"
                  "  commands: integrate, diff; print takes no var\n"
                  "  or no arguments: read '<command> <expr> <var>' lines "
                  "from stdin");
}

} // namespace

int main(int argc, char **argv)
{
    if (argc == 7 && keel::StringRef(argv[1]) == "pade")
        return runPade(argv[2], argv[3], argv[4], std::atoi(argv[5]),
                       std::atoi(argv[6]));
    if (argc == 6 && keel::StringRef(argv[1]) == "pade")
        return runPade(argv[2], argv[3], "", std::atoi(argv[4]),
                       std::atoi(argv[5]));
    if (argc == 6 && keel::StringRef(argv[1]) == "taylor")
        return runTaylor(argv[2], argv[3], argv[4], std::atoi(argv[5]));
    if (argc == 6 && keel::StringRef(argv[1]) == "defint")
        return runDefInt(argv[2], argv[3], argv[4], argv[5]);
    if (argc == 6 && keel::StringRef(argv[1]) == "symsum")
        return runSymSum(argv[2], argv[3], argv[4], argv[5]);
    if (argc == 5 && keel::StringRef(argv[1]) == "taylor")
        return runTaylor(argv[2], argv[3], "", std::atoi(argv[4]));
    if (argc == 5 && keel::StringRef(argv[1]) == "limit")
        return runLimit(argv[2], argv[3], argv[4]);
    if (argc == 5 && keel::StringRef(argv[1]) == "residue")
        return runResidue(argv[2], argv[3], argv[4]);
    if (argc == 5 && keel::StringRef(argv[1]) == "subs")
        return runSubs(argv[2], argv[3], argv[4]);
    if (argc == 5 && keel::StringRef(argv[1]) == "eval")
        return runEval(argv[2], argv[3], argv[4]);
    if (argc == 5 && keel::StringRef(argv[1]) == "laplace")
        return runLaplace(argv[2], argv[3], argv[4], false);
    if (argc == 5 && keel::StringRef(argv[1]) == "ilaplace")
        return runLaplace(argv[2], argv[3], argv[4], true);
    if (argc == 5 && keel::StringRef(argv[1]) == "ztrans")
        return runZTrans(argv[2], argv[3], argv[4], false);
    if (argc == 5 && keel::StringRef(argv[1]) == "iztrans")
        return runZTrans(argv[2], argv[3], argv[4], true);
    if (argc == 5 && keel::StringRef(argv[1]) == "fourier")
        return runFourier(argv[2], argv[3], argv[4], false);
    if (argc == 5 && keel::StringRef(argv[1]) == "ifourier")
        return runFourier(argv[2], argv[3], argv[4], true);
    if (argc == 4)
        return runCommand(argv[1], argv[2], argv[3]);
    if (argc == 3 && keel::StringRef(argv[1]) == "print")
        return runCommand(argv[1], argv[2], "");
    if (argc == 3 && keel::StringRef(argv[1]) == "expand")
        return runCommand(argv[1], argv[2], "");
    if (argc == 3 && keel::StringRef(argv[1]) == "simplify")
        return runCommand(argv[1], argv[2], "");
    if (argc == 3 && keel::StringRef(argv[1]) == "laplace")
        return runLaplace(argv[2], "t", "s", false);
    if (argc == 3 && keel::StringRef(argv[1]) == "ilaplace")
        return runLaplace(argv[2], "s", "t", true);
    if (argc == 3 && keel::StringRef(argv[1]) == "ztrans")
        return runZTrans(argv[2], "n", "z", false);
    if (argc == 3 && keel::StringRef(argv[1]) == "iztrans")
        return runZTrans(argv[2], "z", "n", true);
    if (argc == 3 && keel::StringRef(argv[1]) == "fourier")
        return runFourier(argv[2], "t", "w", false);
    if (argc == 3 && keel::StringRef(argv[1]) == "ifourier")
        return runFourier(argv[2], "w", "t", true);
    if (argc == 3 && keel::StringRef(argv[1]) == "eval")
        return runEval(argv[2], "", "");
    if (argc == 3 && keel::StringRef(argv[1]) == "corpus")
        return runCorpusFile(argv[2]);
    if (argc == 1) {
        keel::String line;
        while (readStdinLine(line)) {
            const keel::StringRef t = trimRef(line);
            if (t.empty())
                continue;
            if (t == "quit" || t == "exit")
                break;
            keel::String cmd, exprSrc, var;
            if (!splitLine(t, cmd, exprSrc, var)) {
                keel::println("malformed line (want: <command> <expr> <var>)");
                continue;
            }
            runCommand(cmd, exprSrc, var);
        }
        return 0;
    }
    usage();
    return 1;
}
