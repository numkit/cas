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
#include <numkit/cas/core/parser.hpp>
#include <numkit/cas/core/series.hpp>
#include <numkit/cas/core/simplify.hpp>
#include <numkit/cas/core/symsolve.hpp>
#include <numkit/cas/integrate/ratint.hpp>
#include <numkit/cas/poly/solve.hpp>
#include <numkit/cas/rubi/rules.hpp>

#include "corpus_runner.hpp"

#include <cstdlib>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <string>
#include <vector>

namespace {

bool isSpace(char ch)
{
    return ch == ' ' || ch == '\t' || ch == '\r' || ch == '\n';
}

std::string trim(const std::string &s)
{
    std::size_t a = 0, b = s.size();
    while (a < b && isSpace(s[a]))
        ++a;
    while (b > a && isSpace(s[b - 1]))
        --b;
    return s.substr(a, b - a);
}

// Split "<command> <expr...> <var>" / "<command> <expr>": the variable
// is the last whitespace-separated token, the expression everything
// between (so expressions may contain spaces).
bool splitLine(const std::string &line, std::string &cmd,
               std::string &exprSrc, std::string &var)
{
    std::vector<std::string> words;
    std::size_t i = 0;
    while (i < line.size()) {
        while (i < line.size() && isSpace(line[i]))
            ++i;
        std::size_t start = i;
        while (i < line.size() && !isSpace(line[i]))
            ++i;
        if (i > start)
            words.push_back(line.substr(start, i - start));
    }
    if (words.empty())
        return false;
    cmd = words.front();
    if (cmd == "print" || cmd == "expand" || cmd == "simplify") {
        exprSrc = trim(line.substr(cmd.size()));
        return !exprSrc.empty();
    }
    if (cmd == "subs" || cmd == "eval") {
        if (cmd == "eval" && words.size() == 2) {
            exprSrc = trim(line.substr(cmd.size()));
            var.clear();
            return !exprSrc.empty();
        }
        // "subs <expr...> <from> <to>" / "eval <expr...> <var> <val>":
        // the last two tokens are the pair, everything between is the
        // expression.
        if (words.size() < 4)
            return false;
        const std::string &to = words.back();
        const std::string &from = words[words.size() - 2];
        const std::size_t toOff = line.rfind(to);
        const std::size_t fromOff = line.rfind(from, toOff);
        exprSrc = trim(line.substr(cmd.size(), fromOff - cmd.size()));
        var = from + "\t" + to; // caller splits on the tab
        return !exprSrc.empty();
    }
    if (words.size() < 3)
        return false;
    var = words.back();
    const std::size_t varOff = line.rfind(var);
    exprSrc = trim(line.substr(cmd.size(), varOff - cmd.size()));
    return !exprSrc.empty();
}

int runSubs(const std::string &exprSrc, const std::string &fromSrc,
            const std::string &toSrc)
{
    numkit::cas::Ctx ctx;
    numkit::cas::Expr f, from, to;
    try {
        f = numkit::cas::parseExpr(ctx, exprSrc);
        from = numkit::cas::parseExpr(ctx, fromSrc);
        to = numkit::cas::parseExpr(ctx, toSrc);
    } catch (const numkit::cas::ParseError &e) {
        std::cout << "parse error at offset " << e.pos() << ": " << e.what()
                  << "\n";
        return 1;
    }
    std::cout << ctx.toString(ctx.subs(f, from, to)) << "\n";
    return 0;
}

int runEval(const std::string &exprSrc, const std::string &varName,
            const std::string &valSrc)
{
    numkit::cas::Ctx ctx;
    numkit::cas::Expr f;
    try {
        f = numkit::cas::parseExpr(ctx, exprSrc);
    } catch (const numkit::cas::ParseError &e) {
        std::cout << "parse error at offset " << e.pos() << ": " << e.what()
                  << "\n";
        return 1;
    }
    std::vector<std::pair<std::string, double>> env;
    if (!varName.empty()) {
        numkit::cas::Expr valExpr;
        try {
            valExpr = numkit::cas::parseExpr(ctx, valSrc);
        } catch (const numkit::cas::ParseError &e) {
            std::cout << "parse error at offset " << e.pos() << ": " << e.what()
                      << "\n";
            return 1;
        }
        double valDbl = 0.0;
        if (!ctx.evalDouble(valExpr, {}, valDbl)) {
            std::cout << "cannot evaluate point: " << valSrc << "\n";
            return 1;
        }
        env.emplace_back(varName, valDbl);
    }
    double out = 0.0;
    if (!ctx.evalDouble(f, env, out)) {
        std::cout << "Unevaluated (domain error, pole, or unresolved symbol)\n";
        return 2;
    }
    std::cout << std::setprecision(16) << out << "\n";
    return 0;
}

int runTaylor(const std::string &exprSrc, const std::string &varName,
              const std::string &x0Src, int order)
{
    numkit::cas::Ctx ctx;
    numkit::cas::Expr f, x0;
    try {
        f = numkit::cas::parseExpr(ctx, exprSrc);
        x0 = x0Src.empty() ? ctx.zero() : numkit::cas::parseExpr(ctx, x0Src);
    } catch (const numkit::cas::ParseError &e) {
        std::cout << "parse error at offset " << e.pos() << ": " << e.what()
                  << "\n";
        return 1;
    }
    const numkit::cas::Expr var = ctx.symbol(varName);
    const numkit::cas::Expr out = numkit::cas::taylor(ctx, f, var, x0, order);
    if (out.isNull()) {
        std::cout << "Unevaluated (pole, branch point, or beyond series domain)\n";
        return 2;
    }
    std::cout << ctx.toString(out) << "\n";
    return 0;
}

int runLimit(const std::string &exprSrc, const std::string &varName,
             const std::string &x0Src)
{
    numkit::cas::Ctx ctx;
    numkit::cas::Expr f, x0;
    try {
        f = numkit::cas::parseExpr(ctx, exprSrc);
        x0 = x0Src.empty() ? ctx.zero() : numkit::cas::parseExpr(ctx, x0Src);
    } catch (const numkit::cas::ParseError &e) {
        std::cout << "parse error at offset " << e.pos() << ": " << e.what()
                  << "\n";
        return 1;
    }
    const numkit::cas::Expr var = ctx.symbol(varName);
    const numkit::cas::LimitResult r = numkit::cas::limit(ctx, f, var, x0);
    if (r.proved()) {
        std::cout << ctx.toString(r.value) << "\n";
        return 0;
    }
    if (r.status == numkit::cas::LimitResult::Status::Divergent) {
        std::cout << "Divergent (pole of order " << r.poleOrder << ")\n";
        return 2;
    }
    std::cout << "Unevaluated: " << r.reason << "\n";
    return 2;
}

int runCommand(const std::string &cmd, const std::string &exprSrc,
               const std::string &varName)
{
    if (cmd == "subs") {
        // splitLine packed "from\tto" into varName
        const std::size_t tab = varName.find('\t');
        return runSubs(exprSrc, varName.substr(0, tab), varName.substr(tab + 1));
    }
    if (cmd == "eval") {
        if (varName.empty())
            return runEval(exprSrc, "", "");
        const std::size_t tab = varName.find('\t');
        return runEval(exprSrc, varName.substr(0, tab), varName.substr(tab + 1));
    }
    numkit::cas::Ctx ctx;
    numkit::cas::Expr f;
    try {
        f = numkit::cas::parseExpr(ctx, exprSrc);
    } catch (const numkit::cas::ParseError &e) {
        std::cout << "parse error at offset " << e.pos() << ": " << e.what()
                  << "\n";
        return 1;
    }
    if (cmd == "print") {
        std::cout << ctx.toString(f) << "\n";
        return 0;
    }
    if (cmd == "expand") {
        std::cout << ctx.toString(ctx.expand(f)) << "\n";
        return 0;
    }
    if (cmd == "simplify") {
        std::cout << ctx.toString(ctx.simplify(f)) << "\n";
        return 0;
    }
    const numkit::cas::Expr var = ctx.symbol(varName);
    if (cmd == "diff") {
        std::cout << ctx.toString(ctx.diff(f, var)) << "\n";
        return 0;
    }
    if (cmd == "taylor")
        return runTaylor(exprSrc, varName, "", 6);
    if (cmd == "limit")
        return runLimit(exprSrc, varName, "");
    if (cmd == "integrate") {
        const numkit::cas::RationalIntegral r =
            numkit::cas::integrate(ctx, f, var);
        if (r.proved()) {
            std::cout << ctx.toString(r.F) << "\n";
            std::cout << "[certificate: PROVED_SYMBOLIC]\n";
            return 0;
        }
        std::cout << "Unevaluated: " << r.reason << "\n";
        return 2;
    }
    if (cmd == "solve") {
        numkit::cas::UPoly N, D;
        if (!numkit::cas::toRational(ctx, f, var, N, D) || !D.isConst()) {
            std::cout << "not a polynomial in " << varName << "\n";
            return 1;
        }
        if (N.isZero()) {
            std::cout << "every point (zero polynomial)\n";
            return 0;
        }
        const auto roots = numkit::cas::solveRealRoots(N);
        if (roots.empty())
            std::cout << "no real roots\n";
        for (const auto &s : roots) {
            if (s.isRational) {
                std::cout << "root #" << s.realIndex << " = "
                          << s.value.toString() << "\n";
            } else {
                std::cout << "root #" << s.realIndex << " in ("
                          << s.interval.lo.toString() << ", "
                          << s.interval.hi.toString() << "]\n";
            }
        }
        return 0;
    }
    if (cmd == "symsolve") {
        const auto roots = numkit::cas::solveSymbolic(ctx, f, var);
        if (roots.empty()) {
            std::cout << "no symbolic solutions found\n";
            return 2;
        }
        for (const auto &r : roots)
            std::cout << ctx.toString(r) << "\n";
        return 0;
    }
    if (cmd == "factor") {
        numkit::cas::Expr factored;
        if (!numkit::cas::factorExpr(ctx, f, var, factored)) {
            std::cout << "not a rational function of " << varName << "\n";
            return 1;
        }
        std::cout << ctx.toString(factored) << "\n";
        return 0;
    }
    if (cmd == "rubi") {
        // Apply the first matching Rubi rule of the committed slice,
        // certified by the Tier-1 gate (dF/dx == integrand).
        const numkit::cas::Expr F =
            numkit::cas::rubi::rubiApply(numkit::cas::rubi::sliceTables(),
                                         ctx, f, var);
        if (F.isNull()) {
            std::cout << "no certified rule application\n";
            return 2;
        }
        std::cout << ctx.toString(F) << "\n";
        std::cout << "[certificate: PROVED_SYMBOLIC]\n";
        return 0;
    }
    std::cout << "unknown command '" << cmd << "' (integrate, diff, subs, print)\n";
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
    std::ifstream in(path);
    if (!in) {
        std::cout << "cannot open corpus file: " << path << "\n";
        return 1;
    }
    std::vector<nkcorpus::CorpusTask> tasks;
    std::size_t lineNo = 0, malformed = 0;
    std::string line;
    while (std::getline(in, line)) {
        ++lineNo;
        nkcorpus::CorpusTask t;
        if (nkcorpus::parseCorpusLine(line, t)) {
            tasks.push_back(std::move(t));
        } else if (nkcorpus::lineKind(line) == nkcorpus::LineKind::Malformed) {
            ++malformed;
            std::cout << "line " << lineNo << "\tMALFORMED_LINE\n";
        }
    }
    std::vector<nkcorpus::TaskOutcome> outcomes;
    const nkcorpus::CorpusReport rep =
        nkcorpus::runCorpus(tasks, &outcomes);
    for (const nkcorpus::TaskOutcome &o : outcomes) {
        std::cout << o.id << '\t' << statusName(o.status) << '\t'
                  << o.micros << "us\t" << o.answerNodes << "nodes";
        if (o.status != nkcorpus::TaskStatus::Proved && !o.detail.empty())
            std::cout << '\t' << o.detail;
        std::cout << '\n';
    }
    std::cout << "----\n"
              << "tasks: " << rep.total << " (+" << malformed
              << " malformed lines)\n"
              << "proved: " << rep.proved << " (" << rep.passRatePct()
              << "%)\n"
              << "unevaluated: " << rep.unevaluated << ", parse errors: "
              << rep.parseErrors << "\n"
              << "verification rate: " << rep.verificationRatePct()
              << "% of integrable\n"
              << "median time: " << rep.medianMicros << "us, p95: "
              << rep.p95Micros << "us\n";
    if (rep.withReference > 0) {
        std::cout << "mean leaf ratio: " << rep.meanLeafRatio << " (over "
                  << rep.withReference << " referenced tasks)\n";
    }
    return 0;
}

void usage()
{
    std::cout << "usage: nkcas <command> <expr> <var>\n"
                 "  commands: integrate, diff; print takes no var\n"
                 "  or no arguments: read '<command> <expr> <var>' lines "
                 "from stdin\n";
}

} // namespace

int main(int argc, char **argv)
{
    if (argc == 6 && std::string(argv[1]) == "taylor")
        return runTaylor(argv[2], argv[3], argv[4], std::atoi(argv[5]));
    if (argc == 5 && std::string(argv[1]) == "taylor")
        return runTaylor(argv[2], argv[3], "", std::atoi(argv[4]));
    if (argc == 5 && std::string(argv[1]) == "limit")
        return runLimit(argv[2], argv[3], argv[4]);
    if (argc == 5 && std::string(argv[1]) == "subs")
        return runSubs(argv[2], argv[3], argv[4]);
    if (argc == 5 && std::string(argv[1]) == "eval")
        return runEval(argv[2], argv[3], argv[4]);
    if (argc == 4)
        return runCommand(argv[1], argv[2], argv[3]);
    if (argc == 3 && std::string(argv[1]) == "print")
        return runCommand(argv[1], argv[2], "");
    if (argc == 3 && std::string(argv[1]) == "expand")
        return runCommand(argv[1], argv[2], "");
    if (argc == 3 && std::string(argv[1]) == "simplify")
        return runCommand(argv[1], argv[2], "");
    if (argc == 3 && std::string(argv[1]) == "eval")
        return runEval(argv[2], "", "");
    if (argc == 3 && std::string(argv[1]) == "corpus")
        return runCorpusFile(argv[2]);
    if (argc == 1) {
        std::string line;
        while (std::getline(std::cin, line)) {
            const std::string t = trim(line);
            if (t.empty())
                continue;
            if (t == "quit" || t == "exit")
                break;
            std::string cmd, exprSrc, var;
            if (!splitLine(t, cmd, exprSrc, var)) {
                std::cout << "malformed line (want: <command> <expr> <var>)\n";
                continue;
            }
            runCommand(cmd, exprSrc, var);
        }
        return 0;
    }
    usage();
    return 1;
}
