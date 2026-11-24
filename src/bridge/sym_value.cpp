// src/bridge/sym_value.cpp — Value bridge and BuiltinClass for numkit::cas.
#include <keel/algo.h>
#include <keel/array.h>
#include <keel/core.h>
#include <keel/format.h>
#include <keel/memory.h>
#include <keel/ref.h>
#include <keel/smart_ptr.h>
#include <keel/string.h>
#include <keel/utf8.h>
#include <keel/math.h>
#include <numkit/cas/sym_value.hpp>

#include <numkit/cas/parse_expr.hpp>
#include <keel/cas/core/series.hpp>
#include <keel/cas/core/simplify.hpp>
#include <keel/cas/core/symsolve.hpp>
#include <keel/cas/integrate/ratint.hpp>
#include <keel/cas/linalg/symmatrix.hpp>
#include <keel/cas/ode/dsolve.hpp>
#include <keel/cas/pde/pdsolve.hpp>
#include <keel/cas/poly/groebner.hpp>
#include <keel/cas/poly/solve.hpp>
#include <keel/cas/poly/zassenhaus.hpp>
#include <keel/cas/transform/fourier.hpp>
#include <keel/cas/transform/laplace.hpp>
#include <keel/cas/transform/ztrans.hpp>

#include <numkit/sys/plugin.hpp>
#include <numkit/value/argcheck.hpp>
#include <numkit/value/error.hpp>


namespace numkit::cas {

using namespace keel::cas;

namespace {

[[noreturn]] void casFail(keel::StringRef id, keel::StringRef msg)
{
    keel::StringRef fn = "sym";
    const keel::usize p1 = id.find(':');
    if (p1 != keel::kInvalidIndex) {
        const keel::StringRef rest = id.substr(p1 + 1);
        const keel::usize p2 = rest.find(':');
        if (p2 != keel::kInvalidIndex) {
            fn = rest.substr(0, p2);
        }
    }
    argcheck::detail::fail(msg, fn, id);
}

keel::Allocator *resolveMr(keel::Allocator *mr) noexcept
{
    return mr ? mr : keel::default_allocator();
}

keel::String trimStr(keel::StringRef s)
{
    keel::usize a = 0, b = s.size();
    while (a < b && keel::is_ascii_space(s.data()[a]))
        ++a;
    while (b > a && keel::is_ascii_space(s.data()[b - 1]))
        --b;
    return keel::String::from(s.substr(a, b - a));
}

keel::String toLowerStr(keel::String s)
{
    for (keel::usize i = 0; i < s.size(); ++i)
        s[i] = keel::to_ascii_lower(s[i]);
    return s;
}

bool isValidIdentifier(keel::StringRef s)
{
    if (s.empty())
        return false;
    if (!(keel::is_ascii_alpha(s[0]) || s[0] == '_'))
        return false;
    for (keel::usize i = 1; i < s.size(); ++i) {
        const char ch = s[i];
        if (!(keel::is_ascii_alnum(ch) || ch == '_'))
            return false;
    }
    return true;
}

struct SymbolNameSet
{
    keel::Array<keel::String> items;

    bool empty() const noexcept { return items.empty(); }
    keel::usize size() const noexcept { return items.size(); }
    const keel::String &front() const noexcept { return items[0]; }
    const keel::String *begin() const noexcept { return items.begin(); }
    const keel::String *end() const noexcept { return items.end(); }

    void insert(keel::StringRef s)
    {
        keel::usize pos = 0;
        while (pos < items.size()) {
            const keel::i32 cmp = items[pos].as_ref().compare(s);
            if (cmp == 0)
                return;
            if (cmp > 0)
                break;
            ++pos;
        }
        items.push_back(keel::String::from(s));
        for (keel::usize i = items.size() - 1; i > pos; --i) {
            keel::swap(items[i], items[i - 1]);
        }
    }
};

Rational doubleToRational(keel::f64 v);

Expr doubleToSymExpr(Ctx &c, keel::f64 v)
{
    if (keel::is_inf(v))
        return (v > 0.0) ? c.symbol("oo") : c.neg(c.symbol("oo"));
    return c.number(doubleToRational(v));
}

Expr complexToSymExpr(Ctx &c, keel::c64 z)
{
    const Expr re = doubleToSymExpr(c, z.re);
    if (z.im == 0.0)
        return re;
    const Expr im = doubleToSymExpr(c, z.im);
    const Expr imPart = c.mul({im, c.symbol("I")});
    if (z.re == 0.0)
        return imPart;
    return c.add({re, imPart});
}

Expr numericElemToSymExpr(Ctx &c, const Value &v, keel::usize idx)
{
    if (v.isComplex())
        return complexToSymExpr(c, v.complexData()[idx]);
    return doubleToSymExpr(c, v.elemAsDouble(idx));
}

bool evalComplexExprRec(const Ctx &c, Expr e, keel::c64 &out)
{
    if (e.isNull())
        return false;
    switch (c.kind(e)) {
    case NodeKind::Number:
        out = keel::c64(c.numberValue(e).toDouble(), 0.0);
        return true;
    case NodeKind::Symbol: {
        const keel::StringRef nm = c.symbolName(e).as_ref();
        if (nm.equals_ignore_ascii_case("i")) { out = keel::c64(0.0, 1.0); return true; }
        if (nm.equals_ignore_ascii_case("pi")) { out = keel::c64(keel::kPi, 0.0); return true; }
        if (nm.equals_ignore_ascii_case("e")) { out = keel::c64(2.71828182845904523536, 0.0); return true; }
        return false;
    }
    case NodeKind::Add: {
        keel::c64 acc(0.0, 0.0);
        for (keel::usize i = 0; i < c.childCount(e); ++i) {
            keel::c64 t;
            if (!evalComplexExprRec(c, c.child(e, i), t))
                return false;
            acc = acc + t;
        }
        out = acc;
        return true;
    }
    case NodeKind::Mul: {
        keel::c64 acc(1.0, 0.0);
        for (keel::usize i = 0; i < c.childCount(e); ++i) {
            keel::c64 t;
            if (!evalComplexExprRec(c, c.child(e, i), t))
                return false;
            acc = acc * t;
        }
        out = acc;
        return true;
    }
    case NodeKind::Pow: {
        keel::c64 b, ex;
        if (!evalComplexExprRec(c, c.child(e, 0), b) ||
            !evalComplexExprRec(c, c.child(e, 1), ex))
            return false;
        out = keel::pow(b, ex);
        return true;
    }
    case NodeKind::Func: {
        if (c.childCount(e) != 1)
            return false;
        keel::c64 a;
        if (!evalComplexExprRec(c, c.child(e, 0), a))
            return false;
        const keel::StringRef fn = c.funcName(e).as_ref();
        if (fn == "exp") { out = keel::exp(a); return true; }
        if (fn == "sin") { out = keel::sin(a); return true; }
        if (fn == "cos") { out = keel::cos(a); return true; }
        if (fn == "tan") { out = keel::tan(a); return true; }
        if (fn == "sinh") { out = keel::sinh(a); return true; }
        if (fn == "cosh") { out = keel::cosh(a); return true; }
        if (fn == "tanh") { out = keel::tanh(a); return true; }
        if (fn == "log" || fn == "ln") { out = keel::log(a); return true; }
        if (fn == "sqrt") { out = keel::sqrt(a); return true; }
        return false;
    }
    case NodeKind::RootOf:
        return false;
    }
    return false;
}

Rational doubleToRational(keel::f64 v)
{
    if (!keel::is_finite(v))
        casFail("nk:sym:nonfinite", "sym: cannot convert non-finite double to exact rational");
    if (v == 0.0)
        return Rational(keel::i64{0});
    const keel::f64 fl = keel::floor(v);
    if (fl == v && keel::abs(v) <= 9.0e15)
        return Rational(keel::as<keel::i64>(v));

    const keel::i32 sign = (v < 0.0) ? -1 : 1;
    const keel::f64 av = keel::abs(v);
    keel::i64 p0 = 0, q0 = 1;
    keel::i64 p1 = 1, q1 = 0;
    keel::f64 x = av;
    for (keel::i32 iter = 0; iter < 32; ++iter) {
        const keel::f64 aDbl = keel::floor(x);
        if (aDbl > 1.0e12)
            break;
        const keel::i64 a = keel::as<keel::i64>(aDbl);
        const keel::i64 p2 = a * p1 + p0;
        const keel::i64 q2 = a * q1 + q0;
        if (q2 <= 0 || q2 > 1000000000LL)
            break;
        p0 = p1;
        q0 = q1;
        p1 = p2;
        q1 = q2;
        const keel::f64 approx = keel::as<keel::f64>(p1) / keel::as<keel::f64>(q1);
        if (keel::abs(approx - av) <= 1e-13 * keel::max(1.0, av))
            break;
        const keel::f64 rem = x - aDbl;
        if (rem <= 1e-15)
            break;
        x = 1.0 / rem;
    }
    return Rational(BigInt(sign * p1), BigInt(q1));
}

Expr parseExprFlexible(Ctx &c, keel::StringRef rawRef, const char *fnName)
{
    keel::String raw = keel::String::from(rawRef);
    keel::String s = trimStr(rawRef);
    if (s.empty())
        casFail(keel::format("nk:{}:emptyExpr", fnName),
                keel::format("{}: symbolic expression string must not be empty", fnName));

    // Support equation strings "lhs == rhs" or "lhs = rhs" -> lhs - (rhs).
    keel::usize eqPos = keel::kInvalidIndex;
    keel::usize eqLen = 0;
    keel::i32 depth = 0;
    for (keel::usize i = 0; i < s.size(); ++i) {
        if (s[i] == '(' || s[i] == '[')
            ++depth;
        else if (s[i] == ')' || s[i] == ']')
            --depth;
        else if (depth == 0 && s[i] == '=') {
            if (i > 0 && (s[i - 1] == '<' || s[i - 1] == '>' || s[i - 1] == '~' || s[i - 1] == '!'))
                continue;
            if (i + 1 < s.size() && s[i + 1] == '=') {
                eqPos = i;
                eqLen = 2;
                break;
            }
            eqPos = i;
            eqLen = 1;
            break;
        }
    }
    if (eqPos != keel::kInvalidIndex) {
        keel::String lhsStr = trimStr(s.as_ref().substr(0, eqPos));
        keel::String rhsStr = trimStr(s.as_ref().substr(eqPos + eqLen));
        try {
            Expr lhs = parseExpr(c, lhsStr);
            Expr rhs = parseExpr(c, rhsStr);
            return c.add({lhs, c.neg(rhs)});
        } catch (const ParseError &e) {
            casFail(keel::format("nk:{}:parseError", fnName),
                    keel::format("{}: parse error in '{}': {}", fnName, raw, e.what()));
        }
    }

    try {
        return parseExpr(c, s);
    } catch (const ParseError &e) {
        casFail(keel::format("nk:{}:parseError", fnName),
                keel::format("{}: parse error in '{}': {}", fnName, raw, e.what()));
    }
}

bool isReservedConstantSymbol(keel::StringRef name)
{
    return name == "pi" || name == "e" || name == "inf" || name == "oo"
           || name == "infinity" || name == "Inf" || name == "i" || name == "j"
           || name == "I";
}

void collectSymbolsRec(const Ctx &c, Expr e, SymbolNameSet &out)
{
    if (e.isNull())
        return;
    const NodeKind k = c.kind(e);
    if (k == NodeKind::Symbol) {
        const keel::String &nm = c.symbolName(e);
        if (!isReservedConstantSymbol(nm))
            out.insert(nm);
        return;
    }
    const keel::usize n = c.childCount(e);
    for (keel::usize i = 0; i < n; ++i)
        collectSymbolsRec(c, c.child(e, i), out);
}

void collectSymbolsFromValue(const Value &v, Ctx &c, SymbolNameSet &out)
{
    if (isSymValue(v)) {
        const keel::usize n = v.objectCount();
        for (keel::usize i = 0; i < n; ++i) {
            const ObjectState *st = v.objectStateAt(i);
            if (st && st->native) {
                auto *sp = static_cast<const SymPayload *>(st->native.get());
                collectSymbolsRec(c, sp->expr, out);
            }
        }
    } else if (v.isChar() || v.isString()) {
        Expr e = parseExprFlexible(c, v.toString(), "symvar");
        collectSymbolsRec(c, e, out);
    }
}

// Rank symbol names by proximity to 'x' (the reference engine's symvar order:
// x, y, z, w, v, u, t, s, ...).
keel::i32 symvarDistance(keel::StringRef a)
{
    if (a.empty())
        return 1000;
    const keel::i32 d = keel::as<keel::i32>(keel::as<keel::u8>(a[0])) - keel::as<keel::i32>('x');
    if (d == 0)
        return 0;
    return (d > 0) ? (2 * d - 1) : (-2 * d);
}

Expr defaultSymVar(Ctx &c, const Value &v, const char *fallback = "x")
{
    SymbolNameSet syms;
    collectSymbolsFromValue(v, c, syms);
    if (syms.empty())
        return c.symbol(fallback);
    keel::StringRef best = syms.front().as_ref();
    for (const auto &s : syms) {
        const keel::i32 ds = symvarDistance(s);
        const keel::i32 db = symvarDistance(best);
        if (ds < db || (ds == db && s.as_ref().compare(best) < 0))
            best = s.as_ref();
    }
    return c.symbol(best);
}

bool parseAssumeDomain(keel::StringRef raw, AssumeDomain &domOut, bool &isClearOut)
{
    isClearOut = false;
    const keel::String s = toLowerStr(trimStr(raw));
    if (s.as_ref() == "clear" || s.as_ref() == "any") {
        domOut = AssumeDomain::Any;
        isClearOut = (s.as_ref() == "clear");
        return true;
    }
    if (s.as_ref() == "real") {
        domOut = AssumeDomain::Real;
        return true;
    }
    if (s.as_ref() == "positive") {
        domOut = AssumeDomain::Positive;
        return true;
    }
    if (s.as_ref() == "negative") {
        domOut = AssumeDomain::Negative;
        return true;
    }
    if (s.as_ref() == "nonnegative") {
        domOut = AssumeDomain::NonNegative;
        return true;
    }
    if (s.as_ref() == "integer") {
        domOut = AssumeDomain::Integer;
        return true;
    }
    return false;
}

template <typename UnaryFn>
Value mapSymUnary(const Value &v, Ctx &c, UnaryFn &&fn,
                  keel::Allocator *mr, const char *fnName)
{
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    if (isSymValue(v)) {
        const keel::usize n = v.objectCount();
        if (n == 0)
            return v;
        if (n == 1 && v.dims().rows() == 1 && v.dims().cols() == 1) {
            Expr in = toSymExpr(v, c, fnName);
            return fromSymExpr(ctxPtr, fn(in), mr);
        }
        keel::Array<keel::Arc<ObjectState>> states(mr);
        states.reserve(n);
        for (keel::usize i = 0; i < n; ++i) {
            const ObjectState *st = v.objectStateAt(i);
            Expr in = (st && st->native)
                          ? static_cast<const SymPayload *>(st->native.get())->expr
                          : c.zero();
            auto nst = keel::make_arc_in<ObjectState>(mr, mr);
            nst->native = keel::make_arc_in<SymPayload>(mr, ctxPtr, fn(in));
            states.push_back(keel::move(nst));
        }
        return Value::objectArray("sym", v.dims(), keel::move(states), /*isHandle=*/false, mr);
    }
    if (v.isNumeric() || v.isLogical()) {
        if (v.isScalar()) {
            Expr in = numericElemToSymExpr(c, v, 0);
            return fromSymExpr(ctxPtr, fn(in), mr);
        }
        const keel::usize n = v.numel();
        keel::Array<keel::Arc<ObjectState>> states(mr);
        states.reserve(n);
        for (keel::usize i = 0; i < n; ++i) {
            Expr in = numericElemToSymExpr(c, v, i);
            auto nst = keel::make_arc_in<ObjectState>(mr, mr);
            nst->native = keel::make_arc_in<SymPayload>(mr, ctxPtr, fn(in));
            states.push_back(keel::move(nst));
        }
        return Value::objectArray("sym", v.dims(), keel::move(states), /*isHandle=*/false, mr);
    }
    if (v.isChar() || v.isString()) {
        Expr in = parseExprFlexible(c, v.toString(), fnName);
        return fromSymExpr(ctxPtr, fn(in), mr);
    }
    casFail(keel::format("nk:{}:invalidType", fnName),
            keel::format("{}: expected sym, numeric, or string argument", fnName));
}

template <typename BinaryFn>
Value mapSymElementwiseBinary(const Value &a, const Value &b, Ctx &c, BinaryFn &&fn,
                              keel::Allocator *mr, const char *fnName)
{
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    SymMatrix A = toSymMatrix(a, c, fnName);
    SymMatrix B = toSymMatrix(b, c, fnName);
    const bool aScalar = (A.rows() == 1 && A.cols() == 1);
    const bool bScalar = (B.rows() == 1 && B.cols() == 1);
    if (aScalar && bScalar) {
        return fromSymExpr(ctxPtr, fn(A(0, 0), B(0, 0)), mr);
    }
    if (aScalar) {
        SymMatrix out(B.rows(), B.cols(), c.zero());
        for (keel::usize r = 0; r < B.rows(); ++r)
            for (keel::usize col = 0; col < B.cols(); ++col)
                out(r, col) = fn(A(0, 0), B(r, col));
        return fromSymMatrix(ctxPtr, out, mr);
    }
    if (bScalar) {
        SymMatrix out(A.rows(), A.cols(), c.zero());
        for (keel::usize r = 0; r < A.rows(); ++r)
            for (keel::usize col = 0; col < A.cols(); ++col)
                out(r, col) = fn(A(r, col), B(0, 0));
        return fromSymMatrix(ctxPtr, out, mr);
    }
    if (A.rows() != B.rows() || A.cols() != B.cols()) {
        casFail(keel::format("nk:{}:dimMismatch", fnName),
                keel::format("{}: matrix dimensions must agree", fnName));
    }
    SymMatrix out(A.rows(), A.cols(), c.zero());
    for (keel::usize r = 0; r < A.rows(); ++r)
        for (keel::usize col = 0; col < A.cols(); ++col)
            out(r, col) = fn(A(r, col), B(r, col));
    return fromSymMatrix(ctxPtr, out, mr);
}

} // namespace

// ============================================================================
// SymPayload & conversion primitives
// ============================================================================

keel::Arc<Ctx> defaultCtx()
{
    static keel::Arc<Ctx> instance = keel::make_arc<Ctx>();
    return instance;
}

keel::Arc<numkit::NativePayload> SymPayload::clone(keel::Allocator *alloc) const
{
    keel::Array<Expr> paramsCopy;
    paramsCopy.reserve(funParams.size());
    for (keel::usize i = 0; i < funParams.size(); ++i)
        paramsCopy.push_back(funParams[i]);
    return keel::make_arc_in<SymPayload>(resolveMr(alloc), ctx, expr, keel::move(paramsCopy));
}

keel::f64 SymPayload::asDouble() const
{
    if (!ctx || expr.isNull())
        return 0.0;
    keel::f64 out = 0.0;
    if (!ctx->evalDouble(expr, {}, out)) {
        casFail("nk:sym:unresolvedSymbol",
                keel::format("double: symbolic expression '{}' contains unresolved symbols or cannot be evaluated to double",
                             ctx->toString(expr)));
    }
    return out;
}

keel::Arc<numkit::NativePayload> SymPayload::fromScalarDouble(keel::f64 v, keel::Allocator *alloc) const
{
    auto c = ctx ? ctx : defaultCtx();
    return keel::make_arc_in<SymPayload>(resolveMr(alloc), c, doubleToSymExpr(*c, v));
}

bool isSymValue(const numkit::Value &v) noexcept
{
    return v.isObject()
        && (v.objectClassNameRef() == "sym" || v.objectClassNameRef() == "symfun");
}

bool isSymfunValue(const numkit::Value &v) noexcept
{
    return v.isObject() && v.objectClassNameRef() == "symfun";
}

Expr toSymExpr(const numkit::Value &v, Ctx &c, const char *fnName)
{
    if (isSymValue(v)) {
        if (v.objectCount() != 1) {
            casFail(keel::format("nk:{}:expectedScalarSym", fnName),
                    keel::format("{}: expected scalar sym expression", fnName));
        }
        const ObjectState *st = v.objectStateConst();
        if (!st || !st->native)
            return c.zero();
        return static_cast<const SymPayload *>(st->native.get())->expr;
    }
    if (v.isNumeric() || v.isLogical()) {
        if (!v.isScalar()) {
            casFail(keel::format("nk:{}:expectedScalar", fnName),
                    keel::format("{}: expected scalar argument", fnName));
        }
        return numericElemToSymExpr(c, v, 0);
    }
    if (v.isChar() || v.isString()) {
        return parseExprFlexible(c, v.toString(), fnName);
    }
    casFail(keel::format("nk:{}:invalidSymArg", fnName),
            keel::format("{}: cannot convert argument to symbolic expression", fnName));
}

SymMatrix toSymMatrix(const numkit::Value &v, Ctx &c, const char *fnName)
{
    if (isSymValue(v)) {
        const keel::usize rows = v.dims().rows();
        const keel::usize cols = v.dims().cols();
        SymMatrix M(rows, cols, c.zero());
        for (keel::usize col = 0; col < cols; ++col) {
            for (keel::usize r = 0; r < rows; ++r) {
                const ObjectState *st = v.objectStateAt(col * rows + r);
                if (st && st->native)
                    M(r, col) = static_cast<const SymPayload *>(st->native.get())->expr;
            }
        }
        return M;
    }
    if (v.isNumeric() || v.isLogical()) {
        if (v.isEmpty())
            return SymMatrix(0, 0);
        const keel::usize rows = v.dims().rows();
        const keel::usize cols = v.dims().cols();
        SymMatrix M(rows, cols, c.zero());
        for (keel::usize col = 0; col < cols; ++col) {
            for (keel::usize r = 0; r < rows; ++r) {
                M(r, col) = numericElemToSymExpr(c, v, col * rows + r);
            }
        }
        return M;
    }
    if (v.isChar() || v.isString()) {
        keel::String s = trimStr(v.toString());
        if (s.size() >= 2 && s[0] == '[' && s[s.size() - 1] == ']') {
            const keel::StringRef body = s.as_ref().substr(1, s.size() - 2);
            keel::Array<keel::Array<Expr>> rowVecs;
            keel::usize rowPos = 0;
            while (rowPos <= body.size()) {
                const keel::StringRef remRows = body.substr(rowPos);
                const keel::usize semi = remRows.find(';');
                const keel::StringRef rowStr = (semi == keel::kInvalidIndex) ? remRows : remRows.substr(0, semi);
                keel::Array<Expr> curRow;
                keel::usize colPos = 0;
                while (colPos <= rowStr.size()) {
                    const keel::StringRef remCols = rowStr.substr(colPos);
                    const keel::usize comma = remCols.find(',');
                    const keel::StringRef colStr = (comma == keel::kInvalidIndex) ? remCols : remCols.substr(0, comma);
                    keel::String item = trimStr(colStr);
                    if (!item.empty())
                        curRow.push_back(parseExprFlexible(c, item, fnName));
                    if (comma == keel::kInvalidIndex)
                        break;
                    colPos += comma + 1;
                }
                if (!curRow.empty())
                    rowVecs.push_back(keel::move(curRow));
                if (semi == keel::kInvalidIndex)
                    break;
                rowPos += semi + 1;
            }
            if (rowVecs.empty())
                return SymMatrix(0, 0);
            const keel::usize rows = rowVecs.size();
            const keel::usize cols = rowVecs[0].size();
            SymMatrix M(rows, cols, c.zero());
            for (keel::usize r = 0; r < rows; ++r) {
                if (rowVecs[r].size() != cols)
                    casFail(keel::format("nk:{}:inconsistentMatrixRow", fnName),
                            keel::format("{}: inconsistent row lengths in symbolic matrix string", fnName));
                for (keel::usize col = 0; col < cols; ++col)
                    M(r, col) = rowVecs[r][col];
            }
            return M;
        }
        Expr e = parseExprFlexible(c, s, fnName);
        return SymMatrix(1, 1, {e});
    }
    if (v.isCell()) {
        const keel::usize rows = v.dims().rows();
        const keel::usize cols = v.dims().cols();
        SymMatrix M(rows, cols, c.zero());
        for (keel::usize col = 0; col < cols; ++col)
            for (keel::usize r = 0; r < rows; ++r)
                M(r, col) = toSymExpr(v.cellAt(col * rows + r), c, fnName);
        return M;
    }
    casFail(keel::format("nk:{}:invalidMatrixArg", fnName),
            keel::format("{}: cannot convert argument to symbolic matrix", fnName));
}

keel::Array<Expr> toSymVector(const numkit::Value &v, Ctx &c, const char *fnName)
{
    if (v.isCell()) {
        keel::Array<Expr> out;
        out.reserve(v.numel());
        for (keel::usize i = 0; i < v.numel(); ++i)
            out.push_back(toSymExpr(v.cellAt(i), c, fnName));
        return out;
    }
    SymMatrix M = toSymMatrix(v, c, fnName);
    keel::Array<Expr> out;
    out.reserve(M.rows() * M.cols());
    for (keel::usize r = 0; r < M.rows(); ++r)
        for (keel::usize col = 0; col < M.cols(); ++col)
            out.push_back(M(r, col));
    return out;
}

numkit::Value fromSymExpr(const keel::Arc<Ctx> &c, Expr e,
                          keel::Allocator *mr)
{
    mr = resolveMr(mr);
    auto st = keel::make_arc_in<ObjectState>(mr, mr);
    st->native = keel::make_arc_in<SymPayload>(mr, c, e);
    return Value::object("sym", keel::move(st), /*isHandle=*/false, mr);
}

numkit::Value fromSymfunExpr(const keel::Arc<Ctx> &c, Expr e,
                             keel::ArrayRef<Expr> params,
                             keel::Allocator *mr)
{
    mr = resolveMr(mr);
    keel::Array<Expr> pvec;
    pvec.reserve(params.size());
    for (keel::usize i = 0; i < params.size(); ++i)
        pvec.push_back(params[i]);
    auto st = keel::make_arc_in<ObjectState>(mr, mr);
    st->native = keel::make_arc_in<SymPayload>(mr, c, e, keel::move(pvec));
    return Value::object("symfun", keel::move(st), /*isHandle=*/false, mr);
}

numkit::Value fromSymMatrix(const keel::Arc<Ctx> &c, const SymMatrix &M,
                            keel::Allocator *mr)
{
    mr = resolveMr(mr);
    const keel::usize rows = M.rows();
    const keel::usize cols = M.cols();
    if (rows == 1 && cols == 1)
        return fromSymExpr(c, M(0, 0), mr);
    keel::Array<keel::Arc<ObjectState>> states(mr);
    states.reserve(rows * cols);
    for (keel::usize col = 0; col < cols; ++col) {
        for (keel::usize r = 0; r < rows; ++r) {
            auto st = keel::make_arc_in<ObjectState>(mr, mr);
            st->native = keel::make_arc_in<SymPayload>(mr, c, M(r, col));
            states.push_back(keel::move(st));
        }
    }
    return Value::objectArray("sym", Dims(rows, cols), keel::move(states), /*isHandle=*/false, mr);
}

numkit::Value fromSymVector(const keel::Arc<Ctx> &c, keel::ArrayRef<Expr> vec,
                            bool column, keel::Allocator *mr)
{
    mr = resolveMr(mr);
    if (vec.size() == 1)
        return fromSymExpr(c, vec[0], mr);
    const keel::usize rows = column ? vec.size() : (vec.empty() ? 0 : 1);
    const keel::usize cols = column ? (vec.empty() ? 0 : 1) : vec.size();
    keel::Array<keel::Arc<ObjectState>> states(mr);
    states.reserve(vec.size());
    for (keel::usize i = 0; i < vec.size(); ++i) {
        auto st = keel::make_arc_in<ObjectState>(mr, mr);
        st->native = keel::make_arc_in<SymPayload>(mr, c, vec[i]);
        states.push_back(keel::move(st));
    }
    return Value::objectArray("sym", Dims(rows, cols), keel::move(states), /*isHandle=*/false, mr);
}

// ============================================================================
// Compute functions with <fn>_argcheck
// ============================================================================

namespace {

void symCreate_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 0, 2, "sym");
}

void symsCommand_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 0, 64, "syms");
}

void symAssume_argcheck(const Value &symVal, keel::StringRef domainStr)
{
    if (!isSymValue(symVal) && !symVal.isChar() && !symVal.isString()) {
        casFail("nk:assume:invalidTarget",
                "assume: first argument must be a symbolic variable");
    }
    AssumeDomain dom = AssumeDomain::Any;
    bool isClr = false;
    if (!parseAssumeDomain(domainStr, dom, isClr)) {
        casFail("nk:assume:invalidDomain",
                keel::format("assume: unknown assumption domain '{}' (expected 'real', 'positive', 'negative', 'nonnegative', 'integer', or 'clear')",
                             domainStr));
    }
}

void symDouble_argcheck(const Value &v)
{
    if (!isSymValue(v) && !v.isNumeric() && !v.isLogical() && !v.isChar() && !v.isString()) {
        casFail("nk:double:invalidType",
                    "double: expected sym, numeric, or string expression");
    }
}

void symVpa_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 1, 2, "vpa");
    if (args.size() == 2) {
        argcheck::expectedPositiveInteger(argcheck::expectedReal(args[1], 2, "d", "vpa"), 2, "d", "vpa");
    }
}

void symFactor_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 1, 2, "factor");
}

void symCollect_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 1, 2, "collect");
}

void symCoeffs_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 1, 2, "coeffs");
}

void symNumden_argcheck(const Value &v)
{
    if (!isSymValue(v) && !v.isNumeric() && !v.isChar() && !v.isString()) {
        casFail("nk:numden:invalidType", "numden: expected symbolic expression");
    }
}

void symPartfrac_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 1, 2, "partfrac");
}

void symSubs_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 2, 3, "subs");
}

void symSymvar_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 1, 2, "symvar");
    if (args.size() == 2) {
        argcheck::expectedPositiveInteger(argcheck::expectedReal(args[1], 2, "n", "symvar"), 2, "n", "symvar");
    }
}

void symPoly2sym_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 1, 2, "poly2sym");
}

void symSym2poly_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 1, 2, "sym2poly");
}

void symDiff_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 1, 3, "diff");
}

void symInt_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 1, 4, "int");
}

void symLimit_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 1, 4, "limit");
}

void symTaylor_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 1, 7, "taylor");
}

void symLaurent_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 1, 4, "laurent");
}

void symMtaylor_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 2, 4, "mtaylor");
}

void symPade_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 1, 5, "pade");
}

void symResidue_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 1, 3, "residue");
}

void symSymsum_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 3, 4, "symsum");
}

void symFiniteDiff_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 1, 4, "finitediff");
}

void symEulerMaclaurin_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 4, 5, "eulermaclaurin");
}

void symSolve_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 1, 64, "solve");
}

void symGroebner_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 1, 3, "groebner");
}

void symPolyReduce_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 2, 4, "polyreduce");
}

} // namespace

numkit::Value symCreate(keel::ArrayRef<numkit::Value> args,
                        keel::Allocator *mr)
{
    symCreate_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    if (args.empty()) {
        return fromSymExpr(ctxPtr, c.zero(), mr);
    }

    const Value &a0 = args[0];
    if (args.size() == 2) {
        const Value &a1 = args[1];
        if (a1.isChar() || a1.isString()) {
            keel::String domStr = a1.toString();
            AssumeDomain dom = AssumeDomain::Any;
            bool isClr = false;
            if (!parseAssumeDomain(domStr, dom, isClr)) {
                casFail("nk:sym:invalidAssumption",
                        keel::format("sym: unknown assumption '{}'", domStr));
            }
            Value out = symCreate(keel::ArrayRef<Value>(&a0, 1), mr);
            SymbolNameSet syms;
            collectSymbolsFromValue(out, c, syms);
            for (const auto &nm : syms) {
                c.assume(nm, dom);
            }
            return out;
        }
        if ((a0.isChar() || a0.isString()) && a1.isNumeric()) {
            keel::String base = trimStr(a0.toString());
            if (!isValidIdentifier(base)) {
                casFail("nk:sym:invalidPrefix",
                        keel::format("sym: matrix symbol prefix '{}' must be a valid identifier", base));
            }
            keel::usize rows = 1, cols = 1;
            if (a1.numel() == 1) {
                keel::i32 n = keel::as<keel::i32>(a1.toScalar());
                if (n < 0)
                    casFail("nk:sym:negativeSize", "sym: dimensions must be non-negative");
                rows = keel::as<keel::usize>(n);
                cols = keel::as<keel::usize>(n);
            } else if (a1.numel() == 2) {
                keel::i32 r = keel::as<keel::i32>(a1.elemAt(0).toScalar());
                keel::i32 col = keel::as<keel::i32>(a1.elemAt(1).toScalar());
                if (r < 0 || col < 0)
                    casFail("nk:sym:negativeSize", "sym: dimensions must be non-negative");
                rows = keel::as<keel::usize>(r);
                cols = keel::as<keel::usize>(col);
            } else {
                casFail("nk:sym:invalidSizeVec", "sym: dimension vector must have 1 or 2 elements");
            }
            SymMatrix M(rows, cols, c.zero());
            for (keel::usize r = 0; r < rows; ++r) {
                for (keel::usize col = 0; col < cols; ++col) {
                    keel::String elemName;
                    if (rows == 1 || cols == 1) {
                        elemName = keel::format("{}{}", base, keel::max(r, col) + 1);
                    } else {
                        elemName = keel::format("{}{}_{}", base, r + 1, col + 1);
                    }
                    M(r, col) = c.symbol(elemName);
                }
            }
            return fromSymMatrix(ctxPtr, M, mr);
        }
        casFail("nk:sym:invalidSecondArg",
                "sym: second argument must be an assumption string or dimension vector");
    }

    if (isSymValue(a0))
        return a0;
    if (a0.isChar() || a0.isString()) {
        keel::String s = trimStr(a0.toString());
        if (s.size() >= 2 && s[0] == '[' && s[s.size() - 1] == ']') {
            return fromSymMatrix(ctxPtr, toSymMatrix(a0, c, "sym"), mr);
        }
        return fromSymExpr(ctxPtr, parseExprFlexible(c, s, "sym"), mr);
    }
    if (a0.isNumeric() || a0.isLogical()) {
        if (a0.isScalar()) {
            return fromSymExpr(ctxPtr, numericElemToSymExpr(c, a0, 0), mr);
        }
        return fromSymMatrix(ctxPtr, toSymMatrix(a0, c, "sym"), mr);
    }
    if (a0.isCell()) {
        return fromSymMatrix(ctxPtr, toSymMatrix(a0, c, "sym"), mr);
    }
    casFail("nk:sym:unsupportedInput", "sym: unsupported input type");
}

void symsCommand(keel::ArrayRef<numkit::Value> args,
                 keel::Array<keel::Pair<keel::String, numkit::Value>> &bindingsOut,
                 keel::Allocator *mr)
{
    symsCommand_argcheck(args);
    mr = resolveMr(mr);
    bindingsOut.clear();
    if (args.empty())
        return;

    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;

    if (args.size() == 1 && (args[0].isChar() || args[0].isString())) {
        keel::String tok = toLowerStr(trimStr(args[0].toString()));
        if (tok.as_ref() == "clear") {
            c.clearAssumptions();
            return;
        }
    }

    bool hasTrailingDomain = false;
    AssumeDomain trailingDom = AssumeDomain::Any;
    bool trailingClear = false;
    keel::usize varEnd = args.size();
    if (args.size() >= 2 && (args[args.size() - 1].isChar() || args[args.size() - 1].isString())) {
        if (parseAssumeDomain(args[args.size() - 1].toString(), trailingDom, trailingClear)) {
            hasTrailingDomain = true;
            varEnd = args.size() - 1;
        }
    }

    // Re-join tokens split across spaces inside parentheses, e.g. `syms f(x, y)`.
    keel::Array<keel::String> joinedTokens;
    {
        keel::String cur;
        keel::i32 depth = 0;
        for (keel::usize i = 0; i < varEnd; ++i) {
            if (!args[i].isChar() && !args[i].isString()) {
                casFail("nk:syms:invalidVarName",
                        "syms: arguments must be variable names (strings)");
            }
            keel::String tok = trimStr(args[i].toString());
            if (depth > 0) {
                cur.append(tok);
                for (char ch : tok) {
                    if (ch == '(') ++depth;
                    else if (ch == ')') --depth;
                }
                if (depth <= 0) {
                    joinedTokens.push_back(keel::move(cur));
                    cur.clear();
                    depth = 0;
                }
                continue;
            }
            keel::i32 d = 0;
            for (char ch : tok) {
                if (ch == '(') ++d;
                else if (ch == ')') --d;
            }
            if (d > 0) {
                cur = keel::move(tok);
                depth = d;
            } else {
                joinedTokens.push_back(keel::move(tok));
            }
        }
        if (!cur.empty())
            joinedTokens.push_back(keel::move(cur));
    }

    auto hasBinding = [&](keel::StringRef nm) -> bool {
        for (const auto &kv : bindingsOut)
            if (kv.first.as_ref() == nm)
                return true;
        return false;
    };

    for (keel::usize i = 0; i < joinedTokens.size(); ++i) {
        const keel::String &rawTok = joinedTokens[i];
        const keel::usize lp = rawTok.as_ref().find('(');
        if (lp != keel::kInvalidIndex && !rawTok.empty() && rawTok.back() == ')') {
            keel::String fnName = trimStr(rawTok.as_ref().substr(0, lp));
            keel::String argBody = trimStr(rawTok.as_ref().substr(lp + 1, rawTok.size() - lp - 2));
            if (!isValidIdentifier(fnName) || argBody.empty()) {
                casFail("nk:syms:invalidIdentifier",
                        keel::format("syms: '{}' is not a valid variable name", rawTok));
            }
            keel::Array<Expr> paramExprs;
            keel::usize pos = 0;
            while (pos <= argBody.size()) {
                const keel::usize comma = argBody.as_ref().find(',', pos);
                const keel::StringRef seg = (comma == keel::kInvalidIndex)
                                                ? argBody.as_ref().substr(pos)
                                                : argBody.as_ref().substr(pos, comma - pos);
                keel::String pname = trimStr(seg);
                if (!isValidIdentifier(pname)) {
                    casFail("nk:syms:invalidIdentifier",
                            keel::format("syms: '{}' is not a valid variable name", rawTok));
                }
                Expr psym = c.symbol(pname);
                if (hasTrailingDomain)
                    c.assume(pname, trailingDom);
                if (!hasBinding(pname.as_ref()))
                    bindingsOut.emplace_back(pname.clone(), fromSymExpr(ctxPtr, psym, mr));
                paramExprs.push_back(psym);
                if (comma == keel::kInvalidIndex)
                    break;
                pos = comma + 1;
            }
            Expr fnExpr = c.func(fnName, paramExprs);
            bindingsOut.emplace_back(keel::move(fnName),
                                     fromSymfunExpr(ctxPtr, fnExpr, paramExprs.as_ref(), mr));
            continue;
        }
        if (!isValidIdentifier(rawTok)) {
            casFail("nk:syms:invalidIdentifier",
                    keel::format("syms: '{}' is not a valid variable name", rawTok));
        }
        Expr s = c.symbol(rawTok);
        if (hasTrailingDomain) {
            c.assume(rawTok, trailingDom);
        }
        bindingsOut.emplace_back(rawTok.clone(), fromSymExpr(ctxPtr, s, mr));
    }
}

numkit::Value symfunCreate(keel::ArrayRef<numkit::Value> args,
                           keel::Allocator *mr)
{
    argcheck::checkNargin(args.size(), 2, 64, "symfun");
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    Expr body = toSymExpr(args[0], c, "symfun");
    keel::Array<Expr> params;
    for (keel::usize i = 1; i < args.size(); ++i) {
        keel::Array<Expr> part = toSymVector(args[i], c, "symfun");
        for (const Expr p : part) {
            if (c.kind(p) != NodeKind::Symbol) {
                casFail("nk:symfun:invalidInput",
                        "symfun: input variables must be symbolic variables");
            }
            params.push_back(p);
        }
    }
    if (params.empty()) {
        casFail("nk:symfun:invalidInput", "symfun: at least one input variable is required");
    }
    return fromSymfunExpr(ctxPtr, body, params.as_ref(), mr);
}

numkit::Value symFormula(const numkit::Value &v, keel::Allocator *mr)
{
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    return fromSymExpr(ctxPtr, toSymExpr(v, c, "formula"), mr);
}

numkit::Value symArgnames(const numkit::Value &v, keel::Allocator *mr)
{
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    if (isSymfunValue(v)) {
        const ObjectState *st = v.objectStateConst();
        if (st && st->native) {
            auto *sp = static_cast<const SymPayload *>(st->native.get());
            return fromSymVector(ctxPtr, sp->funParams.as_ref(), /*column=*/false, mr);
        }
    }
    keel::Array<Expr> empty;
    return fromSymVector(ctxPtr, empty.as_ref(), /*column=*/false, mr);
}

numkit::Value symLhs(const numkit::Value &v, keel::Allocator *mr)
{
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    Expr e = toSymExpr(v, c, "lhs");
    if (c.kind(e) == NodeKind::Func && c.childCount(e) == 2) {
        const keel::StringRef fn = c.funcName(e).as_ref();
        if (fn == "__eq" || fn == "__ne" || fn == "__lt" ||
            fn == "__le" || fn == "__gt" || fn == "__ge") {
            return fromSymExpr(ctxPtr, c.child(e, 0), mr);
        }
    }
    casFail("nk:lhs:notEquation", "lhs: argument must be a symbolic equation or inequality");
}

numkit::Value symRhs(const numkit::Value &v, keel::Allocator *mr)
{
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    Expr e = toSymExpr(v, c, "rhs");
    if (c.kind(e) == NodeKind::Func && c.childCount(e) == 2) {
        const keel::StringRef fn = c.funcName(e).as_ref();
        if (fn == "__eq" || fn == "__ne" || fn == "__lt" ||
            fn == "__le" || fn == "__gt" || fn == "__ge") {
            return fromSymExpr(ctxPtr, c.child(e, 1), mr);
        }
    }
    casFail("nk:rhs:notEquation", "rhs: argument must be a symbolic equation or inequality");
}

numkit::Value symIsAlways(const numkit::Value &v, keel::Allocator *mr)
{
    mr = resolveMr(mr);
    if (v.isLogical())
        return v;
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    auto evalRel = [&](Expr e) -> bool {
        if (c.kind(e) == NodeKind::Func && c.childCount(e) == 2) {
            const keel::StringRef fn = c.funcName(e).as_ref();
            const Expr diff = simplify(c, c.add({c.child(e, 0), c.neg(c.child(e, 1))}));
            if (fn == "__eq")
                return c.isZero(diff);
            if (fn == "__ne")
                return !c.isZero(diff);
            keel::f64 dv = 0.0;
            if (c.evalDouble(diff, {}, dv)) {
                if (fn == "__lt") return dv < 0.0;
                if (fn == "__le") return dv <= 0.0;
                if (fn == "__gt") return dv > 0.0;
                if (fn == "__ge") return dv >= 0.0;
            }
            if (fn == "__gt") return c.isAssumedPositive(diff);
            if (fn == "__ge") return c.isZero(diff) || c.isAssumedPositive(diff) || c.isAssumedNonNegative(diff);
            if (fn == "__lt") return c.isAssumedNegative(diff);
            if (fn == "__le") return c.isZero(diff) || c.isAssumedNegative(diff);
        }
        return !c.isZero(simplify(c, e));
    };
    SymMatrix M = toSymMatrix(v, c, "isAlways");
    if (M.rows() == 1 && M.cols() == 1)
        return Value::logicalScalar(evalRel(M(0, 0)), mr);
    Value out = Value::matrix(M.rows(), M.cols(), ValueType::LOGICAL, mr);
    keel::u8 *dst = out.logicalDataMut();
    for (keel::usize col = 0; col < M.cols(); ++col)
        for (keel::usize r = 0; r < M.rows(); ++r)
            dst[col * M.rows() + r] = evalRel(M(r, col)) ? 1 : 0;
    return out;
}

keel::String symMatlabFunctionSource(keel::ArrayRef<numkit::Value> args,
                                     keel::Allocator *mr)
{
    argcheck::checkNargin(args.size(), 1, 16, "matlabFunction");
    (void)mr;
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;

    SymMatrix M = toSymMatrix(args[0], c, "matlabFunction");

    // Parse optional 'Vars' name-value pair.
    bool hasVars = false;
    Value varsArg;
    for (keel::usize i = 1; i + 1 < args.size(); i += 2) {
        if (args[i].isChar() || args[i].isString()) {
            keel::String key = toLowerStr(trimStr(args[i].toString()));
            if (key.as_ref() == "vars") {
                hasVars = true;
                varsArg = args[i + 1];
            }
        }
    }

    // Build parameter list and any vector-element substitutions (e.g. {t, [y1; y2]} -> @(t, in2)).
    keel::Array<keel::String> paramNames;
    keel::Array<keel::Pair<Expr, keel::String>> vecSubsts;
    if (hasVars) {
        if (varsArg.isCell()) {
            for (keel::usize i = 0; i < varsArg.numel(); ++i) {
                const Value &el = varsArg.cellAt(i);
                keel::Array<Expr> ev = toSymVector(el, c, "matlabFunction");
                if (ev.size() == 1 && c.kind(ev[0]) == NodeKind::Symbol) {
                    paramNames.push_back(c.symbolName(ev[0]).clone());
                } else {
                    keel::String pname = keel::format("in{}", i + 1);
                    paramNames.push_back(pname.clone());
                    for (keel::usize k = 0; k < ev.size(); ++k) {
                        vecSubsts.emplace_back(ev[k], keel::format("{}({})", pname, k + 1));
                    }
                }
            }
        } else {
            keel::Array<Expr> ev = toSymVector(varsArg, c, "matlabFunction");
            for (const Expr v : ev) {
                if (c.kind(v) == NodeKind::Symbol)
                    paramNames.push_back(c.symbolName(v).clone());
            }
        }
    } else if (isSymfunValue(args[0])) {
        const ObjectState *st = args[0].objectStateConst();
        if (st && st->native) {
            auto *sp = static_cast<const SymPayload *>(st->native.get());
            for (keel::usize i = 0; i < sp->funParams.size(); ++i) {
                if (c.kind(sp->funParams[i]) == NodeKind::Symbol)
                    paramNames.push_back(c.symbolName(sp->funParams[i]).clone());
            }
        }
    } else {
        SymbolNameSet syms;
        for (keel::usize r = 0; r < M.rows(); ++r)
            for (keel::usize col = 0; col < M.cols(); ++col)
                collectSymbolsRec(c, M(r, col), syms);
        for (const auto &nm : syms)
            paramNames.push_back(nm.clone());
    }

    // Apply vector-parameter substitutions using unique placeholder symbols, then replace in text.
    keel::Array<keel::Pair<keel::String, keel::String>> textRepls;
    for (keel::usize i = 0; i < vecSubsts.size(); ++i) {
        keel::String ph = keel::format("__nk_mf_arg_{}__", i);
        Expr phSym = c.symbol(ph);
        for (keel::usize r = 0; r < M.rows(); ++r)
            for (keel::usize col = 0; col < M.cols(); ++col)
                M(r, col) = c.subs(M(r, col), vecSubsts[i].first, phSym);
        textRepls.emplace_back(keel::move(ph), vecSubsts[i].second.clone());
    }

    auto vectorizeExprStr = [&](Expr e) -> keel::String {
        keel::String raw = c.toString(e);
        // Replace vector placeholder symbols first.
        for (const auto &rp : textRepls) {
            keel::String next;
            keel::usize pos = 0;
            while (pos < raw.size()) {
                const keel::usize f = raw.as_ref().find(rp.first.as_ref(), pos);
                if (f == keel::kInvalidIndex) {
                    next.append(raw.as_ref().substr(pos));
                    break;
                }
                next.append(raw.as_ref().substr(pos, f - pos));
                next.append(rp.second);
                pos = f + rp.first.size();
            }
            raw = keel::move(next);
        }
        // Vectorize *, /, ^ -> .*, ./, .^ and standalone I -> 1i, oo -> inf.
        keel::String out;
        out.reserve(raw.size() + 16);
        for (keel::usize i = 0; i < raw.size(); ++i) {
            const char ch = raw[i];
            if ((ch == '*' || ch == '/' || ch == '^') && (i == 0 || raw[i - 1] != '.')) {
                out.push_back('.');
                out.push_back(ch);
            } else if (keel::is_ascii_alpha(ch) || ch == '_') {
                keel::usize j = i + 1;
                while (j < raw.size() && (keel::is_ascii_alnum(raw[j]) || raw[j] == '_'))
                    ++j;
                const keel::StringRef id = raw.as_ref().substr(i, j - i);
                if (id == "I")
                    out.append("1i");
                else if (id == "oo")
                    out.append("inf");
                else
                    out.append(id);
                i = j - 1;
            } else {
                out.push_back(ch);
            }
        }
        return out;
    };

    keel::String src = keel::String::from("@(");
    for (keel::usize i = 0; i < paramNames.size(); ++i) {
        if (i > 0) src.append(",");
        src.append(paramNames[i]);
    }
    src.append(") ");
    if (M.rows() == 1 && M.cols() == 1) {
        src.append(vectorizeExprStr(M(0, 0)));
    } else {
        src.push_back('[');
        for (keel::usize r = 0; r < M.rows(); ++r) {
            if (r > 0) src.append("; ");
            for (keel::usize col = 0; col < M.cols(); ++col) {
                if (col > 0) src.append(", ");
                src.append(vectorizeExprStr(M(r, col)));
            }
        }
        src.push_back(']');
    }
    return src;
}

numkit::Value symAssume(const numkit::Value &symVal, keel::StringRef domainStr,
                        keel::Allocator *mr)
{
    symAssume_argcheck(symVal, domainStr);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    AssumeDomain dom = AssumeDomain::Any;
    bool isClr = false;
    parseAssumeDomain(domainStr, dom, isClr);
    SymbolNameSet syms;
    collectSymbolsFromValue(symVal, c, syms);
    if (syms.empty()) {
        casFail("nk:assume:noSymbol", "assume: target does not contain any symbolic variable");
    }
    for (const auto &nm : syms) {
        c.assume(nm, dom);
    }
    return fromSymExpr(ctxPtr, c.symbol(syms.front()), mr);
}

numkit::Value symAssumeCond(const numkit::Value &condVal,
                            keel::Allocator *mr)
{
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    SymMatrix M = toSymMatrix(condVal, c, "assume");
    for (keel::usize r = 0; r < M.rows(); ++r) {
        for (keel::usize col = 0; col < M.cols(); ++col) {
            const Expr e = M(r, col);
            if (c.kind(e) == NodeKind::Func && c.childCount(e) == 2) {
                const keel::String &fn = c.funcName(e);
                const Expr lhs = c.child(e, 0);
                const Expr rhs = c.child(e, 1);
                if (c.kind(lhs) == NodeKind::Symbol && c.isZero(rhs)) {
                    if (fn == "__gt")
                        c.assume(c.symbolName(lhs), AssumeDomain::Positive);
                    else if (fn == "__ge")
                        c.assume(c.symbolName(lhs), AssumeDomain::NonNegative);
                    else if (fn == "__lt")
                        c.assume(c.symbolName(lhs), AssumeDomain::Negative);
                    else if (fn == "__le")
                        c.assume(c.symbolName(lhs), AssumeDomain::Real);
                } else if (c.kind(rhs) == NodeKind::Symbol && c.isZero(lhs)) {
                    if (fn == "__lt")
                        c.assume(c.symbolName(rhs), AssumeDomain::Positive);
                    else if (fn == "__le")
                        c.assume(c.symbolName(rhs), AssumeDomain::NonNegative);
                    else if (fn == "__gt")
                        c.assume(c.symbolName(rhs), AssumeDomain::Negative);
                    else if (fn == "__ge")
                        c.assume(c.symbolName(rhs), AssumeDomain::Real);
                } else {
                    SymbolNameSet syms;
                    collectSymbolsRec(c, e, syms);
                    for (const auto &nm : syms)
                        c.assume(nm, AssumeDomain::Real);
                }
            } else {
                SymbolNameSet syms;
                collectSymbolsRec(c, e, syms);
                for (const auto &nm : syms)
                    c.assume(nm, AssumeDomain::Real);
            }
        }
    }
    return condVal;
}

keel::String symEvalSource(const numkit::Value &v)
{
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    auto isIdChar = [](char ch) -> bool {
        return (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') ||
               (ch >= '0' && ch <= '9') || ch == '_';
    };
    auto fmtOne = [&](Expr e) -> keel::String {
        keel::String s = c.toString(e);
        // Replace standalone symbolic imaginary unit 'I' with '1i'.
        keel::String out;
        out.reserve(s.size() + 8);
        for (keel::usize i = 0; i < s.size(); ++i) {
            if (s[i] == 'I') {
                const bool prevId = (i > 0) && isIdChar(s[i - 1]);
                const bool nextId = (i + 1 < s.size()) && isIdChar(s[i + 1]);
                if (!prevId && !nextId) {
                    out.append("1i");
                    continue;
                }
            }
            out.push_back(s[i]);
        }
        return out;
    };
    SymMatrix M = toSymMatrix(v, c, "eval");
    if (M.rows() == 1 && M.cols() == 1)
        return fmtOne(M(0, 0));
    keel::String out;
    out.push_back('[');
    for (keel::usize r = 0; r < M.rows(); ++r) {
        if (r > 0)
            out.append("; ");
        for (keel::usize col = 0; col < M.cols(); ++col) {
            if (col > 0)
                out.append(", ");
            out.append(fmtOne(M(r, col)));
        }
    }
    out.push_back(']');
    return out;
}

numkit::Value symAssumptions(const numkit::Value &symVal,
                             keel::Allocator *mr)
{
    if (!isSymValue(symVal) && !symVal.isChar() && !symVal.isString()) {
        casFail("nk:assumptions:invalidTarget",
                "assumptions: expected a symbolic variable");
    }
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    Expr e = toSymExpr(symVal, c, "assumptions");
    if (c.kind(e) != NodeKind::Symbol) {
        casFail("nk:assumptions:notSymbol",
                "assumptions: expected a single symbolic variable");
    }
    switch (c.assumption(e)) {
    case AssumeDomain::Real:
        return Value::fromString("real", mr);
    case AssumeDomain::Positive:
        return Value::fromString("positive", mr);
    case AssumeDomain::Negative:
        return Value::fromString("negative", mr);
    case AssumeDomain::NonNegative:
        return Value::fromString("nonnegative", mr);
    case AssumeDomain::Integer:
        return Value::fromString("integer", mr);
    case AssumeDomain::Any:
    default:
        return Value::fromString("any", mr);
    }
}

numkit::Value symDouble(const numkit::Value &v,
                        keel::Allocator *mr)
{
    symDouble_argcheck(v);
    mr = resolveMr(mr);
    if (v.isNumeric() || v.isLogical()) {
        if (v.isScalar())
            return Value::scalar(v.toScalar(), mr);
        Value out = Value::matrix(v.dims().rows(), v.dims().cols(), ValueType::DOUBLE, mr);
        keel::f64 *dst = out.doubleDataMut();
        for (keel::usize i = 0; i < v.numel(); ++i)
            dst[i] = v.elemAt(i).toScalar();
        return out;
    }
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    if (isSymValue(v)) {
        const keel::usize n = v.objectCount();
        if (n == 0)
            return Value::matrix(v.dims().rows(), v.dims().cols(), ValueType::DOUBLE, mr);
        if (n == 1 && v.dims().rows() == 1 && v.dims().cols() == 1) {
            Expr e = toSymExpr(v, c, "double");
            keel::f64 val = 0.0;
            if (c.evalDouble(e, {}, val))
                return Value::scalar(val, mr);
            keel::c64 z;
            if (evalComplexExprRec(c, e, z)) {
                if (keel::abs(z.im) <= 1e-15 * keel::max(1.0, keel::abs(z.re)))
                    return Value::scalar(z.re, mr);
                return Value::complexScalar(z.re, z.im, mr);
            }
            casFail("nk:double:unresolvedSymbol",
                    keel::format("double: cannot convert symbolic expression '{}' to double", c.toString(e)));
        }
        keel::Array<keel::c64> cvals(mr);
        cvals.reserve(n);
        bool anyComplex = false;
        for (keel::usize i = 0; i < n; ++i) {
            const ObjectState *st = v.objectStateAt(i);
            Expr e = (st && st->native)
                         ? static_cast<const SymPayload *>(st->native.get())->expr
                         : c.zero();
            keel::f64 val = 0.0;
            if (c.evalDouble(e, {}, val)) {
                cvals.push_back(keel::c64(val, 0.0));
                continue;
            }
            keel::c64 z;
            if (evalComplexExprRec(c, e, z)) {
                if (keel::abs(z.im) > 1e-15 * keel::max(1.0, keel::abs(z.re)))
                    anyComplex = true;
                else
                    z.im = 0.0;
                cvals.push_back(z);
                continue;
            }
            casFail("nk:double:unresolvedSymbol",
                    keel::format("double: cannot convert symbolic element '{}' to double", c.toString(e)));
        }
        if (anyComplex) {
            Value out = Value::matrix(v.dims().rows(), v.dims().cols(), ValueType::COMPLEX, mr);
            keel::c64 *dst = out.complexDataMut();
            for (keel::usize i = 0; i < n; ++i) dst[i] = cvals[i];
            return out;
        }
        Value out = Value::matrix(v.dims().rows(), v.dims().cols(), ValueType::DOUBLE, mr);
        keel::f64 *dst = out.doubleDataMut();
        for (keel::usize i = 0; i < n; ++i) dst[i] = cvals[i].re;
        return out;
    }
    Expr e = parseExprFlexible(c, v.toString(), "double");
    keel::f64 val = 0.0;
    if (!c.evalDouble(e, {}, val)) {
        casFail("nk:double:unresolvedSymbol",
                keel::format("double: cannot convert symbolic expression '{}' to double", c.toString(e)));
    }
    return Value::scalar(val, mr);
}

numkit::Value symVpa(keel::ArrayRef<numkit::Value> args,
                     keel::Allocator *mr)
{
    symVpa_argcheck(args);
    return symDouble(args[0], mr);
}

numkit::Value symChar(const numkit::Value &v,
                      keel::Allocator *mr)
{
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    if (isSymValue(v)) {
        if (v.objectCount() == 1 && v.dims().rows() == 1 && v.dims().cols() == 1) {
            return Value::fromString(c.toString(toSymExpr(v, c, "char")), mr);
        }
        return Value::fromString(toSymMatrix(v, c, "char").toString(c), mr);
    }
    if (v.isChar() || v.isString())
        return Value::fromString(v.toString(), mr);
    Expr e = toSymExpr(v, c, "char");
    return Value::fromString(c.toString(e), mr);
}

numkit::Value symLatex(const numkit::Value &v,
                       keel::Allocator *mr)
{
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    Expr e = toSymExpr(v, c, "latex");
    return Value::fromString(toLatex(c, e), mr);
}

numkit::Value symCCode(const numkit::Value &v,
                       keel::Allocator *mr)
{
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    Expr e = toSymExpr(v, c, "ccode");
    return Value::fromString(toCCode(c, e), mr);
}

numkit::Value symPretty(const numkit::Value &v,
                        keel::Allocator *mr)
{
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    if (isSymValue(v)) {
        if (v.objectCount() == 1 && v.dims().rows() == 1 && v.dims().cols() == 1) {
            return Value::fromString(c.toString(toSymExpr(v, c, "pretty")), mr);
        }
        return Value::fromString(toSymMatrix(v, c, "pretty").toString(c), mr);
    }
    if (v.isChar() || v.isString())
        return Value::fromString(v.toString(), mr);
    Expr e = toSymExpr(v, c, "pretty");
    return Value::fromString(c.toString(e), mr);
}

numkit::Value symSimplify(const numkit::Value &v,
                          keel::Allocator *mr)
{
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    return mapSymUnary(v, c, [&](Expr e) {
        if (c.leafCount(e) > 256)
            return e;
        SymbolNameSet syms;
        collectSymbolsRec(c, e, syms);
        if (syms.size() > 6 && c.leafCount(e) > 64)
            return e;
        Budget b(4096);
        return simplify(c, e, &b);
    }, mr, "simplify");
}

numkit::Value symExpand(const numkit::Value &v,
                        keel::Allocator *mr)
{
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    return mapSymUnary(v, c, [&](Expr e) { return c.expand(e); }, mr, "expand");
}

void symFactor(keel::ArrayRef<numkit::Value> args, keel::usize nargout,
               keel::MutArrayRef<numkit::Value> outs,
               keel::Allocator *mr)
{
    symFactor_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    Expr f = toSymExpr(args[0], c, "factor");
    keel::Array<Expr> vars;
    if (args.size() >= 2) {
        vars = toSymVector(args[1], c, "factor");
    }
    FactorMultiResult res = factorMulti(c, f, vars);
    if (!res.proved()) {
        outs[0] = fromSymExpr(ctxPtr, f, mr);
        if (nargout >= 2 && outs.size() >= 2)
            outs[1] = Value::scalar(1.0, mr);
        return;
    }
    if (nargout <= 1) {
        keel::Array<Expr> facList;
        if (res.content != Rational(keel::i64{1}) || res.factors.empty()) {
            facList.push_back(c.number(res.content));
        }
        for (const auto &it : res.factors) {
            for (keel::i32 m = 0; m < it.multiplicity; ++m)
                facList.push_back(it.factor);
        }
        outs[0] = fromSymVector(ctxPtr, facList, /*column=*/false, mr);
    } else {
        keel::Array<Expr> facList;
        keel::Array<keel::f64> mults;
        if (res.content != Rational(keel::i64{1}) || res.factors.empty()) {
            facList.push_back(c.number(res.content));
            mults.push_back(1.0);
        }
        for (const auto &it : res.factors) {
            facList.push_back(it.factor);
            mults.push_back(keel::as<keel::f64>(it.multiplicity));
        }
        outs[0] = fromSymVector(ctxPtr, facList, /*column=*/false, mr);
        Value mVal = Value::matrix(1, mults.size(), ValueType::DOUBLE, mr);
        keel::f64 *mp = mVal.doubleDataMut();
        for (keel::usize i = 0; i < mults.size(); ++i)
            mp[i] = mults[i];
        outs[1] = keel::move(mVal);
    }
}

numkit::Value symCollect(keel::ArrayRef<numkit::Value> args,
                         keel::Allocator *mr)
{
    symCollect_argcheck(args);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    Expr var = (args.size() >= 2) ? toSymExpr(args[1], c, "collect")
                                  : defaultSymVar(c, args[0]);
    return mapSymUnary(args[0], c, [&](Expr e) { return collect(c, e, var); }, mr, "collect");
}

void symCoeffs(keel::ArrayRef<numkit::Value> args, keel::usize nargout,
               keel::MutArrayRef<numkit::Value> outs,
               keel::Allocator *mr)
{
    symCoeffs_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    Expr e = toSymExpr(args[0], c, "coeffs");
    Expr var = (args.size() >= 2) ? toSymExpr(args[1], c, "coeffs")
                                  : defaultSymVar(c, args[0]);
    PolyCoeffsResult res = coeffs(c, e, var);
    outs[0] = fromSymVector(ctxPtr, res.coefficients, /*column=*/false, mr);
    if (nargout >= 2 && outs.size() >= 2) {
        outs[1] = fromSymVector(ctxPtr, res.terms, /*column=*/false, mr);
    }
}

void symNumden(const numkit::Value &v, keel::usize nargout,
               keel::MutArrayRef<numkit::Value> outs,
               keel::Allocator *mr)
{
    symNumden_argcheck(v);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    SymMatrix M = toSymMatrix(v, c, "numden");
    SymMatrix N(M.rows(), M.cols(), c.zero());
    SymMatrix D(M.rows(), M.cols(), c.one());
    for (keel::usize r = 0; r < M.rows(); ++r) {
        for (keel::usize col = 0; col < M.cols(); ++col) {
            NumDenResult nd = numden(c, M(r, col));
            N(r, col) = nd.num;
            D(r, col) = nd.den;
        }
    }
    outs[0] = fromSymMatrix(ctxPtr, N, mr);
    if (nargout >= 2 && outs.size() >= 2) {
        outs[1] = fromSymMatrix(ctxPtr, D, mr);
    }
}

numkit::Value symPartfrac(keel::ArrayRef<numkit::Value> args,
                          keel::Allocator *mr)
{
    symPartfrac_argcheck(args);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    Expr var = (args.size() >= 2) ? toSymExpr(args[1], c, "partfrac")
                                  : defaultSymVar(c, args[0]);
    return mapSymUnary(args[0], c, [&](Expr e) {
        Expr pf = partfrac(c, e, var);
        return pf.isNull() ? e : pf;
    }, mr, "partfrac");
}

namespace {

Expr subsMultiRec(Ctx &c, Expr e, keel::ArrayRef<Expr> fromList, keel::ArrayRef<Expr> toList)
{
    for (keel::usize i = 0; i < fromList.size(); ++i) {
        if (e == fromList[i])
            return toList[i];
    }
    switch (c.kind(e)) {
    case NodeKind::Number:
    case NodeKind::Symbol:
    case NodeKind::RootOf:
        return e;
    case NodeKind::Func: {
        if (c.funcName(e) == "diff" && (c.childCount(e) == 2 || c.childCount(e) == 3)) {
            const Expr dvar = c.child(e, 1);
            for (keel::usize i = 0; i < fromList.size(); ++i) {
                if (fromList[i] == dvar && fromList[i] != toList[i])
                    return c.func("subs", {e, fromList[i], toList[i]});
            }
        }
        keel::Array<Expr> kids;
        kids.reserve(c.childCount(e));
        for (keel::usize i = 0; i < c.childCount(e); ++i)
            kids.push_back(subsMultiRec(c, c.child(e, i), fromList, toList));
        return c.func(c.funcName(e), kids);
    }
    case NodeKind::Pow:
        return c.pow(subsMultiRec(c, c.child(e, 0), fromList, toList),
                     subsMultiRec(c, c.child(e, 1), fromList, toList));
    case NodeKind::Add:
    case NodeKind::Mul: {
        keel::Array<Expr> kids;
        kids.reserve(c.childCount(e));
        for (keel::usize i = 0; i < c.childCount(e); ++i)
            kids.push_back(subsMultiRec(c, c.child(e, i), fromList, toList));
        return c.kind(e) == NodeKind::Add ? c.add(kids) : c.mul(kids);
    }
    }
    return e;
}

} // namespace

numkit::Value symSubs(keel::ArrayRef<numkit::Value> args,
                      keel::Allocator *mr)
{
    symSubs_argcheck(args);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    keel::Array<Expr> fromList;
    keel::Array<Expr> toList;
    const Value *broadcastTarget = nullptr;
    if (args.size() == 2) {
        fromList.push_back(defaultSymVar(c, args[0]));
        toList = toSymVector(args[1], c, "subs");
        if (toList.size() > 1)
            broadcastTarget = &args[1];
    } else {
        fromList = toSymVector(args[1], c, "subs");
        toList = toSymVector(args[2], c, "subs");
        if (fromList.size() == 1 && toList.size() > 1) {
            broadcastTarget = &args[2];
        } else if (fromList.size() != toList.size()) {
            casFail("nk:subs:lengthMismatch",
                    "subs: old and new substitution lists must have the same number of elements");
        }
    }
    if (broadcastTarget != nullptr) {
        SymMatrix S = toSymMatrix(args[0], c, "subs");
        if (S.rows() == 1 && S.cols() == 1) {
            SymMatrix T = toSymMatrix(*broadcastTarget, c, "subs");
            SymMatrix out(T.rows(), T.cols());
            for (keel::usize r = 0; r < T.rows(); ++r) {
                for (keel::usize col = 0; col < T.cols(); ++col)
                    out(r, col) = c.subs(S(0, 0), fromList[0], T(r, col));
            }
            return fromSymMatrix(ctxPtr, out, resolveMr(mr));
        }
        casFail("nk:subs:lengthMismatch",
                "subs: old and new substitution lists must have the same number of elements");
    }
    if (fromList.size() == 1) {
        return mapSymUnary(args[0], c, [&](Expr e) {
            return c.subs(e, fromList[0], toList[0]);
        }, mr, "subs");
    }
    return mapSymUnary(args[0], c, [&](Expr e) {
        return subsMultiRec(c, e, fromList.as_ref(), toList.as_ref());
    }, mr, "subs");
}

numkit::Value symSymvar(keel::ArrayRef<numkit::Value> args,
                        keel::Allocator *mr)
{
    symSymvar_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    SymbolNameSet syms;
    collectSymbolsFromValue(args[0], c, syms);
    keel::Array<keel::String> sorted = keel::move(syms.items);
    if (args.size() == 2) {
        const keel::usize n = keel::as<keel::usize>(args[1].toScalar());
        keel::sort(sorted.begin(), sorted.end(), [](const keel::String &a, const keel::String &b) {
            const keel::i32 da = symvarDistance(a);
            const keel::i32 db = symvarDistance(b);
            return (da != db) ? (da < db) : (a.as_ref().compare(b.as_ref()) < 0);
        });
        while (sorted.size() > n)
            sorted.pop_back();
    }
    keel::Array<Expr> exprs;
    exprs.reserve(sorted.size());
    for (const auto &nm : sorted)
        exprs.push_back(c.symbol(nm));
    return fromSymVector(ctxPtr, exprs, /*column=*/false, mr);
}

numkit::Value symPoly2sym(keel::ArrayRef<numkit::Value> args,
                          keel::Allocator *mr)
{
    symPoly2sym_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    keel::Array<Expr> cf = toSymVector(args[0], c, "poly2sym");
    Expr var = (args.size() >= 2) ? toSymExpr(args[1], c, "poly2sym") : c.symbol("x");
    if (cf.empty())
        return fromSymExpr(ctxPtr, c.zero(), mr);
    const keel::usize n = cf.size();
    keel::Array<Expr> terms;
    terms.reserve(n);
    for (keel::usize i = 0; i < n; ++i) {
        const keel::usize deg = n - 1 - i;
        Expr mon = (deg == 0) ? c.one() : c.pow(var, c.number(keel::as<keel::i64>(deg)));
        terms.push_back(c.mul({cf[i], mon}));
    }
    return fromSymExpr(ctxPtr, c.add(terms), mr);
}

numkit::Value symSym2poly(keel::ArrayRef<numkit::Value> args,
                          keel::Allocator *mr)
{
    symSym2poly_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    Expr p = toSymExpr(args[0], c, "sym2poly");
    Expr var = (args.size() >= 2) ? toSymExpr(args[1], c, "sym2poly")
                                  : defaultSymVar(c, args[0]);
    PolyCoeffsResult res = coeffs(c, p, var);
    if (res.dense.empty()) {
        return Value::scalar(0.0, mr);
    }
    const keel::usize n = res.dense.size();
    Value out = Value::matrix(1, n, ValueType::DOUBLE, mr);
    keel::f64 *dst = out.doubleDataMut();
    for (keel::usize i = 0; i < n; ++i) {
        const Expr &ce = res.dense[n - 1 - i];
        keel::f64 val = 0.0;
        if (!c.evalDouble(ce, {}, val)) {
            casFail("nk:sym2poly:nonNumericCoeff",
                    keel::format("sym2poly: polynomial coefficient '{}' is not numeric", c.toString(ce)));
        }
        dst[i] = val;
    }
    return out;
}

numkit::Value symDiff(keel::ArrayRef<numkit::Value> args,
                      keel::Allocator *mr)
{
    symDiff_argcheck(args);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    Expr var;
    bool varSpecified = false;
    keel::i32 order = 1;
    if (args.size() == 2) {
        if (args[1].isNumeric() && args[1].isScalar()) {
            order = keel::as<keel::i32>(args[1].toScalar());
        } else {
            var = toSymExpr(args[1], c, "diff");
            varSpecified = true;
        }
    } else if (args.size() == 3) {
        if (args[1].isNumeric() && args[1].isScalar()) {
            order = keel::as<keel::i32>(args[1].toScalar());
            var = toSymExpr(args[2], c, "diff");
            varSpecified = true;
        } else {
            var = toSymExpr(args[1], c, "diff");
            varSpecified = true;
            if (!args[2].isNumeric() || !args[2].isScalar()) {
                casFail("nk:diff:invalidOrder", "diff: differentiation order must be a non-negative integer");
            }
            order = keel::as<keel::i32>(args[2].toScalar());
        }
    }
    if (!varSpecified) {
        if (isSymfunValue(args[0])) {
            const ObjectState *st = args[0].objectStateConst();
            if (st && st->native) {
                auto *sp = static_cast<const SymPayload *>(st->native.get());
                if (!sp->funParams.empty())
                    var = sp->funParams[0];
            }
        }
        if (var.isNull())
            var = defaultSymVar(c, args[0]);
    }
    if (order < 0) {
        casFail("nk:diff:negativeOrder", "diff: differentiation order must be >= 0");
    }
    if (c.kind(var) != NodeKind::Symbol) {
        casFail("nk:diff:invalidVar", "diff: differentiation variable must be a symbol");
    }
    auto diffStep = [&](Expr e) -> Expr {
        auto hasKnownBuiltinFunc = [](keel::StringRef name) -> bool {
            return name == "__eq" || name == "__ne" || name == "__lt" || name == "__le" ||
                   name == "__gt" || name == "__ge" || name == "diff" ||
                   name == "sin" || name == "cos" || name == "tan" || name == "sec" || name == "csc" || name == "cot" ||
                   name == "asin" || name == "acos" || name == "atan" || name == "acsc" || name == "asec" || name == "acot" ||
                   name == "sinh" || name == "cosh" || name == "tanh" || name == "sech" || name == "csch" || name == "coth" ||
                   name == "asinh" || name == "acosh" || name == "atanh" || name == "acsch" || name == "asech" || name == "acoth" ||
                   name == "exp" || name == "log" || name == "sqrt" || name == "abs" || name == "sign" ||
                   name == "erf" || name == "erfc" || name == "erfi" || name == "gamma" || name == "lgamma" ||
                   name == "heaviside" || name == "dirac" || name == "zeta" || name == "Ei" ||
                   name == "besselJ" || name == "besselY" || name == "besselI" || name == "besselK" ||
                   name == "airyAi" || name == "airyBi" || name == "legendreP" || name == "legendreQ" ||
                   name == "chebyshevT" || name == "chebyshevU" || name == "hermiteH" || name == "laguerreL" ||
                   name == "Si" || name == "Ci" || name == "Shi" || name == "Chi" || name == "Li" || name == "li" ||
                   name == "fresnelS" || name == "fresnelC" || name == "polylog" || name == "hypergeom2F1" ||
                   name == "lambertw" || name == "dF" || name == "dF2" || name == "ddF" || name == "ddF2";
        };
        struct AbstractDiffer {
            Ctx &ctx;
            Expr v;
            decltype(hasKnownBuiltinFunc) &isKnown;
            bool containsAbstract(Expr ex) const
            {
                if (ex.isNull())
                    return false;
                if (ctx.kind(ex) == NodeKind::Func && !isKnown(ctx.funcName(ex)))
                    return true;
                for (keel::usize i = 0; i < ctx.childCount(ex); ++i) {
                    if (containsAbstract(ctx.child(ex, i)))
                        return true;
                }
                return false;
            }
            Expr run(Expr ex) const
            {
                if (!containsAbstract(ex))
                    return ctx.diff(ex, v);
                switch (ctx.kind(ex)) {
                case NodeKind::Number:
                case NodeKind::RootOf:
                    return ctx.zero();
                case NodeKind::Symbol:
                    return (ex == v) ? ctx.one() : ctx.zero();
                case NodeKind::Add: {
                    keel::Array<Expr> parts;
                    parts.reserve(ctx.childCount(ex));
                    for (keel::usize i = 0; i < ctx.childCount(ex); ++i) {
                        Expr di = run(ctx.child(ex, i));
                        if (di.isNull()) return Expr();
                        parts.push_back(di);
                    }
                    return ctx.add(parts);
                }
                case NodeKind::Mul: {
                    const keel::usize n = ctx.childCount(ex);
                    keel::Array<Expr> sumTerms;
                    sumTerms.reserve(n);
                    for (keel::usize i = 0; i < n; ++i) {
                        Expr di = run(ctx.child(ex, i));
                        if (di.isNull()) return Expr();
                        if (ctx.isZero(di)) continue;
                        keel::Array<Expr> prod;
                        prod.reserve(n);
                        for (keel::usize j = 0; j < n; ++j)
                            prod.push_back(i == j ? di : ctx.child(ex, j));
                        sumTerms.push_back(ctx.mul(prod));
                    }
                    return sumTerms.empty() ? ctx.zero() : ctx.add(sumTerms);
                }
                case NodeKind::Pow: {
                    const Expr base = ctx.child(ex, 0);
                    const Expr exp = ctx.child(ex, 1);
                    const Expr db = run(base);
                    const Expr de = run(exp);
                    if (db.isNull() || de.isNull()) return Expr();
                    if (ctx.isZero(de)) {
                        if (ctx.isZero(db)) return ctx.zero();
                        return ctx.mul({exp, ctx.pow(base, ctx.add({exp, ctx.neg(ctx.one())})), db});
                    }
                    return ctx.mul({ex, ctx.add({ctx.mul({de, ctx.func("log", base)}),
                                                 ctx.div(ctx.mul({exp, db}), base)})});
                }
                case NodeKind::Func: {
                    const keel::String &fn = ctx.funcName(ex);
                    if (ctx.childCount(ex) == 2 &&
                        (fn == "__eq" || fn == "__ne" || fn == "__lt" ||
                         fn == "__le" || fn == "__gt" || fn == "__ge")) {
                        Expr dl = run(ctx.child(ex, 0));
                        Expr dr = run(ctx.child(ex, 1));
                        if (dl.isNull() || dr.isNull()) return Expr();
                        return ctx.func(fn, dl, dr);
                    }
                    if (fn == "diff" && ctx.childCount(ex) == 2) {
                        if (ctx.child(ex, 1) == v)
                            return ctx.func("diff", {ctx.child(ex, 0), v, ctx.number(keel::i64{2})});
                        Expr df = run(ctx.child(ex, 0));
                        return ctx.isZero(df) ? ctx.zero() : ctx.func("diff", {ex, v});
                    }
                    if (fn == "diff" && ctx.childCount(ex) == 3) {
                        if (ctx.child(ex, 1) == v)
                            return ctx.func("diff", {ctx.child(ex, 0), v, ctx.add({ctx.child(ex, 2), ctx.one()})});
                        Expr df = run(ctx.child(ex, 0));
                        return ctx.isZero(df) ? ctx.zero() : ctx.func("diff", {ex, v});
                    }
                    if (ctx.childCount(ex) == 1) {
                        const Expr u = ctx.child(ex, 0);
                        const Expr du = run(u);
                        if (du.isNull()) return Expr();
                        if (ctx.isZero(du)) return ctx.zero();
                        if (!isKnown(fn)) {
                            return (u == v) ? ctx.func("diff", ex, v)
                                            : ctx.mul({ctx.func("diff", ex, u), du});
                        }
                        // Known unary function applied to abstract inner expression: chain rule
                        const Expr dummy = ctx.symbol("__nk_diff_u__");
                        const Expr outerD = ctx.diff(ctx.func(fn, dummy), dummy);
                        if (outerD.isNull()) return Expr();
                        return ctx.mul({ctx.subs(outerD, dummy, u), du});
                    }
                    return Expr();
                }
                }
                return Expr();
            }
        };
        AbstractDiffer differ{c, var, hasKnownBuiltinFunc};
        return differ.run(e);
    };
    if (isSymfunValue(args[0])) {
        const ObjectState *st = args[0].objectStateConst();
        if (st && st->native) {
            auto *sp = static_cast<const SymPayload *>(st->native.get());
            Expr cur = sp->expr;
            for (keel::i32 k = 0; k < order; ++k) {
                cur = diffStep(cur);
                if (cur.isNull()) {
                    casFail("nk:diff:unsupported", "diff: cannot differentiate expression");
                }
            }
            return fromSymfunExpr(ctxPtr, cur, sp->funParams.as_ref(), mr);
        }
    }
    return mapSymUnary(args[0], c, [&](Expr e) {
        Expr cur = e;
        for (keel::i32 k = 0; k < order; ++k) {
            cur = diffStep(cur);
            if (cur.isNull()) {
                casFail("nk:diff:unsupported", "diff: cannot differentiate expression");
            }
        }
        return cur;
    }, mr, "diff");
}

numkit::Value symInt(keel::ArrayRef<numkit::Value> args,
                     keel::Allocator *mr)
{
    symInt_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    Expr var = defaultSymVar(c, args[0]);
    bool isDefinite = false;
    Expr aBound, bBound;

    if (args.size() == 2) {
        if ((args[1].isNumeric() || isSymValue(args[1])) && args[1].numel() == 2) {
            keel::Array<Expr> bnds = toSymVector(args[1], c, "int");
            aBound = bnds[0];
            bBound = bnds[1];
            isDefinite = true;
        } else {
            var = toSymExpr(args[1], c, "int");
        }
    } else if (args.size() == 3) {
        if ((args[2].isNumeric() || isSymValue(args[2])) && args[2].numel() == 2) {
            var = toSymExpr(args[1], c, "int");
            keel::Array<Expr> bnds = toSymVector(args[2], c, "int");
            aBound = bnds[0];
            bBound = bnds[1];
            isDefinite = true;
        } else {
            aBound = toSymExpr(args[1], c, "int");
            bBound = toSymExpr(args[2], c, "int");
            isDefinite = true;
        }
    } else if (args.size() == 4) {
        var = toSymExpr(args[1], c, "int");
        aBound = toSymExpr(args[2], c, "int");
        bBound = toSymExpr(args[3], c, "int");
        isDefinite = true;
    }

    if (c.kind(var) != NodeKind::Symbol) {
        casFail("nk:int:invalidVar", "int: integration variable must be a symbol");
    }

    if (!isDefinite) {
        return mapSymUnary(args[0], c, [&](Expr e) {
            RationalIntegral ri = integrate(c, e, var);
            if (!ri.proved()) {
                casFail("nk:int:unevaluated",
                        keel::format("int: could not find closed-form antiderivative for '{}' ({})",
                                     c.toString(e), ri.reason));
            }
            return ri.F;
        }, mr, "int");
    }

    return mapSymUnary(args[0], c, [&](Expr e) {
        DefiniteIntegral di = definiteIntegrate(c, e, var, aBound, bBound);
        if (di.status == DefiniteIntegral::Status::Divergent) {
            casFail("nk:int:divergent",
                    keel::format("int: definite integral is divergent ({})", di.reason));
        }
        if (!di.proved()) {
            casFail("nk:int:unevaluated",
                    keel::format("int: could not evaluate definite integral ({})", di.reason));
        }
        return di.value;
    }, mr, "int");
}

numkit::Value symLimit(keel::ArrayRef<numkit::Value> args,
                       keel::Allocator *mr)
{
    symLimit_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    Expr f = toSymExpr(args[0], c, "limit");
    Expr var = defaultSymVar(c, args[0]);
    Expr x0 = c.zero();
    keel::i32 dir = 0;

    if (args.size() == 2) {
        x0 = toSymExpr(args[1], c, "limit");
    } else if (args.size() >= 3) {
        var = toSymExpr(args[1], c, "limit");
        x0 = toSymExpr(args[2], c, "limit");
        if (args.size() == 4) {
            if (!args[3].isChar() && !args[3].isString()) {
                casFail("nk:limit:invalidDir",
                        "limit: direction must be 'left' or 'right'");
            }
            keel::String dStr = toLowerStr(trimStr(args[3].toString()));
            if (dStr.as_ref() == "right" || dStr.as_ref() == "+")
                dir = +1;
            else if (dStr.as_ref() == "left" || dStr.as_ref() == "-")
                dir = -1;
            else
                casFail("nk:limit:invalidDir",
                        keel::format("limit: direction must be 'left' or 'right', got '{}'", dStr));
        }
    }

    LimitResult res = (dir == 0) ? limit(c, f, var, x0)
                                 : limitOneSided(c, f, var, x0, dir);
    if (res.status == LimitResult::Status::Divergent) {
        return fromSymExpr(ctxPtr, c.symbol("inf"), mr);
    }
    if (!res.proved()) {
        casFail("nk:limit:unevaluated",
                keel::format("limit: could not determine symbolic limit ({})", res.reason));
    }
    return fromSymExpr(ctxPtr, res.value, mr);
}

numkit::Value symTaylor(keel::ArrayRef<numkit::Value> args,
                        keel::Allocator *mr)
{
    symTaylor_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    Expr f = toSymExpr(args[0], c, "taylor");
    Expr var = defaultSymVar(c, args[0]);
    Expr x0 = c.zero();
    keel::i32 order = 5;

    // Support both positional (f, [var], [x0], [order]) and Name-Value ('ExpansionPoint', x0, 'Order', n).
    keel::usize posEnd = args.size();
    for (keel::usize i = 1; i + 1 < args.size(); ++i) {
        if (args[i].isChar() || args[i].isString()) {
            keel::String key = toLowerStr(trimStr(args[i].toString()));
            if (key.as_ref() == "expansionpoint" || key.as_ref() == "order") {
                posEnd = i;
                break;
            }
        }
    }
    if (posEnd == 2) {
        if (args[1].isNumeric() && args[1].isScalar()) {
            order = keel::as<keel::i32>(args[1].toScalar());
        } else {
            var = toSymExpr(args[1], c, "taylor");
        }
    } else if (posEnd == 3) {
        var = toSymExpr(args[1], c, "taylor");
        if (args[2].isNumeric() && args[2].isScalar()) {
            order = keel::as<keel::i32>(args[2].toScalar());
        } else {
            x0 = toSymExpr(args[2], c, "taylor");
        }
    } else if (posEnd >= 4) {
        var = toSymExpr(args[1], c, "taylor");
        x0 = toSymExpr(args[2], c, "taylor");
        order = keel::as<keel::i32>(args[3].toScalar());
    }

    for (keel::usize i = posEnd; i + 1 < args.size(); i += 2) {
        keel::String key = toLowerStr(trimStr(args[i].toString()));
        if (key.as_ref() == "expansionpoint") {
            x0 = toSymExpr(args[i + 1], c, "taylor");
        } else if (key.as_ref() == "order") {
            keel::i32 ordArg = keel::as<keel::i32>(args[i + 1].toScalar());
            if (ordArg <= 0)
                casFail("nk:taylor:invalidOrder", "taylor: 'Order' must be a positive integer");
            order = ordArg - 1;
        } else {
            casFail("nk:taylor:unknownOption",
                    keel::format("taylor: unknown option '{}'", args[i].toString()));
        }
    }

    Expr out = taylor(c, f, var, x0, order);
    if (out.isNull()) {
        casFail("nk:taylor:failed", "taylor: series expansion failed (pole or branch point at expansion point)");
    }
    return fromSymExpr(ctxPtr, out, mr);
}

numkit::Value symLaurent(keel::ArrayRef<numkit::Value> args,
                         keel::Allocator *mr)
{
    symLaurent_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    Expr f = toSymExpr(args[0], c, "laurent");
    Expr var = (args.size() >= 2) ? toSymExpr(args[1], c, "laurent") : defaultSymVar(c, args[0]);
    Expr x0 = (args.size() >= 3) ? toSymExpr(args[2], c, "laurent") : c.zero();
    keel::i32 order = (args.size() >= 4) ? keel::as<keel::i32>(args[3].toScalar()) : 5;
    Expr out = laurent(c, f, var, x0, order);
    if (out.isNull()) {
        casFail("nk:laurent:failed", "laurent: series expansion failed");
    }
    return fromSymExpr(ctxPtr, out, mr);
}

numkit::Value symMtaylor(keel::ArrayRef<numkit::Value> args,
                         keel::Allocator *mr)
{
    symMtaylor_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    Expr f = toSymExpr(args[0], c, "mtaylor");
    keel::Array<Expr> vars = toSymVector(args[1], c, "mtaylor");
    keel::Array<Expr> x0s(vars.size(), c.zero());
    keel::i32 order = 4;
    if (args.size() == 3) {
        if (args[2].isNumeric() && args[2].isScalar() && vars.size() > 1) {
            order = keel::as<keel::i32>(args[2].toScalar());
        } else {
            x0s = toSymVector(args[2], c, "mtaylor");
        }
    } else if (args.size() >= 4) {
        x0s = toSymVector(args[2], c, "mtaylor");
        order = keel::as<keel::i32>(args[3].toScalar());
    }
    Expr out = mtaylor(c, f, vars, x0s, order);
    if (out.isNull()) {
        casFail("nk:mtaylor:failed", "mtaylor: multivariate Taylor expansion failed");
    }
    return fromSymExpr(ctxPtr, out, mr);
}

void symPade(keel::ArrayRef<numkit::Value> args, keel::usize nargout,
             keel::MutArrayRef<numkit::Value> outs,
             keel::Allocator *mr)
{
    symPade_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    Expr f = toSymExpr(args[0], c, "pade");
    Expr var = (args.size() >= 2) ? toSymExpr(args[1], c, "pade") : defaultSymVar(c, args[0]);
    Expr x0 = (args.size() >= 3) ? toSymExpr(args[2], c, "pade") : c.zero();
    keel::i32 m = 3, n = 3;
    if (args.size() == 4) {
        keel::Array<Expr> ord = toSymVector(args[3], c, "pade");
        if (ord.size() == 2) {
            keel::f64 md = 3.0, nd = 3.0;
            c.evalDouble(ord[0], {}, md);
            c.evalDouble(ord[1], {}, nd);
            m = keel::as<keel::i32>(md);
            n = keel::as<keel::i32>(nd);
        } else {
            m = keel::as<keel::i32>(args[3].toScalar());
            n = m;
        }
    } else if (args.size() >= 5) {
        m = keel::as<keel::i32>(args[3].toScalar());
        n = keel::as<keel::i32>(args[4].toScalar());
    }
    PadeResult res = pade(c, f, var, x0, m, n);
    if (!res.proved()) {
        casFail("nk:pade:failed", keel::format("pade: could not construct Pade approximant ({})", res.reason));
    }
    if (nargout == 2 && outs.size() >= 2) {
        outs[0] = fromSymExpr(ctxPtr, res.numerator, mr);
        outs[1] = fromSymExpr(ctxPtr, res.denominator, mr);
    } else {
        outs[0] = fromSymExpr(ctxPtr, res.value, mr);
        if (nargout >= 3 && outs.size() >= 3) {
            outs[1] = fromSymExpr(ctxPtr, res.numerator, mr);
            outs[2] = fromSymExpr(ctxPtr, res.denominator, mr);
        }
    }
}

numkit::Value symResidue(keel::ArrayRef<numkit::Value> args,
                         keel::Allocator *mr)
{
    symResidue_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    Expr f = toSymExpr(args[0], c, "residue");
    Expr var = (args.size() >= 2) ? toSymExpr(args[1], c, "residue") : defaultSymVar(c, args[0]);
    Expr z0 = (args.size() >= 3) ? toSymExpr(args[2], c, "residue") : c.zero();
    Expr out = residue(c, f, var, z0);
    if (out.isNull()) {
        casFail("nk:residue:failed", "residue: could not compute symbolic residue");
    }
    return fromSymExpr(ctxPtr, out, mr);
}

numkit::Value symSymsum(keel::ArrayRef<numkit::Value> args,
                        keel::Allocator *mr)
{
    symSymsum_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    Expr f = toSymExpr(args[0], c, "symsum");
    Expr var, a, b;
    if (args.size() == 3) {
        var = defaultSymVar(c, args[0], "k");
        a = toSymExpr(args[1], c, "symsum");
        b = toSymExpr(args[2], c, "symsum");
    } else {
        var = toSymExpr(args[1], c, "symsum");
        a = toSymExpr(args[2], c, "symsum");
        b = toSymExpr(args[3], c, "symsum");
    }
    SymSumResult res = symsum(c, f, var, a, b);
    if (res.status == SymSumResult::Status::Divergent) {
        return fromSymExpr(ctxPtr, c.symbol("inf"), mr);
    }
    if (!res.proved()) {
        casFail("nk:symsum:unevaluated", keel::format("symsum: could not evaluate symbolic sum ({})", res.reason));
    }
    return fromSymExpr(ctxPtr, res.value, mr);
}

numkit::Value symFiniteDiff(keel::ArrayRef<numkit::Value> args,
                            keel::Allocator *mr)
{
    symFiniteDiff_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    Expr f = toSymExpr(args[0], c, "finitediff");
    Expr var = (args.size() >= 2) ? toSymExpr(args[1], c, "finitediff") : defaultSymVar(c, args[0]);
    keel::i32 order = (args.size() >= 3) ? keel::as<keel::i32>(args[2].toScalar()) : 1;
    Expr step = (args.size() >= 4) ? toSymExpr(args[3], c, "finitediff") : c.one();
    Expr out = finiteDiff(c, f, var, order, step);
    if (out.isNull()) {
        casFail("nk:finitediff:failed", "finitediff: invalid order or variable");
    }
    return fromSymExpr(ctxPtr, out, mr);
}

numkit::Value symEulerMaclaurin(keel::ArrayRef<numkit::Value> args,
                                keel::Allocator *mr)
{
    symEulerMaclaurin_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    Expr f = toSymExpr(args[0], c, "eulermaclaurin");
    Expr var = toSymExpr(args[1], c, "eulermaclaurin");
    Expr a = toSymExpr(args[2], c, "eulermaclaurin");
    Expr b = toSymExpr(args[3], c, "eulermaclaurin");
    keel::i32 order = (args.size() >= 5) ? keel::as<keel::i32>(args[4].toScalar()) : 4;
    EulerMaclaurinResult res = eulerMaclaurin(c, f, var, a, b, order);
    if (res.approximation.isNull()) {
        casFail("nk:eulermaclaurin:failed", "eulermaclaurin: could not construct Euler-Maclaurin expansion");
    }
    return fromSymExpr(ctxPtr, res.approximation, mr);
}

void symSolve(keel::ArrayRef<numkit::Value> args, keel::usize nargout,
              keel::MutArrayRef<numkit::Value> outs,
              keel::Allocator *mr)
{
    symSolve_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;

    auto isPureVarArg = [&](const Value &v) -> bool {
        if (isSymValue(v)) {
            const keel::usize n = v.objectCount();
            if (n == 0)
                return false;
            for (keel::usize i = 0; i < n; ++i) {
                const ObjectState *st = v.objectStateAt(i);
                if (!st || !st->native)
                    return false;
                const Expr e = static_cast<const SymPayload *>(st->native.get())->expr;
                if (c.kind(e) != NodeKind::Symbol || isReservedConstantSymbol(c.symbolName(e)))
                    return false;
            }
            return true;
        }
        if (v.isChar() || v.isString()) {
            keel::String s = trimStr(v.toString());
            if (s.empty())
                return false;
            if (!keel::is_ascii_alpha(s[0]) && s[0] != '_')
                return false;
            for (keel::usize i = 1; i < s.size(); ++i)
                if (!keel::is_ascii_alnum(s[i]) && s[i] != '_')
                    return false;
            return !isReservedConstantSymbol(s);
        }
        return false;
    };

    // Split variadic arguments into leading equation arguments and trailing variable arguments:
    //   solve(eq1, eq2, [x y])  |  solve(eq1, eq2, x, y)  |  solve([eq1, eq2], [x y])  |  solve(eq)
    keel::usize varStart = args.size();
    if (args.size() >= 2) {
        while (varStart > 1 && isPureVarArg(args[varStart - 1]))
            --varStart;
    }

    keel::Array<Expr> eqs;
    for (keel::usize i = 0; i < varStart; ++i) {
        keel::Array<Expr> part = toSymVector(args[i], c, "solve");
        for (Expr e : part) {
            if (c.kind(e) == NodeKind::Func && c.childCount(e) == 2 && c.funcName(e) == "__eq")
                e = c.add({c.child(e, 0), c.neg(c.child(e, 1))});
            eqs.push_back(e);
        }
    }

    keel::Array<Expr> vars;
    if (varStart < args.size()) {
        for (keel::usize i = varStart; i < args.size(); ++i) {
            keel::Array<Expr> part = toSymVector(args[i], c, "solve");
            for (const Expr v : part)
                vars.push_back(v);
        }
    } else {
        SymbolNameSet symSet;
        for (const auto &eq : eqs)
            collectSymbolsRec(c, eq, symSet);
        if (eqs.size() == 1) {
            vars.push_back(defaultSymVar(c, args[0]));
        } else {
            for (const auto &nm : symSet)
                vars.push_back(c.symbol(nm));
        }
    }

    if (eqs.size() == 1 && vars.size() == 1) {
        keel::Array<Expr> roots = solveSymbolic(c, eqs[0], vars[0]);
        outs[0] = fromSymVector(ctxPtr, roots, /*column=*/true, mr);
        return;
    }

    keel::Array<keel::Array<Expr>> tuples = solveSystem(c, eqs, vars);
    const keel::usize k = vars.size();
    if (nargout >= k && k > 1 && outs.size() >= k) {
        for (keel::usize j = 0; j < k; ++j) {
            keel::Array<Expr> colVec;
            colVec.reserve(tuples.size());
            for (const auto &t : tuples)
                if (j < t.size())
                    colVec.push_back(t[j]);
            outs[j] = fromSymVector(ctxPtr, colVec, /*column=*/true, mr);
        }
        return;
    }

    Value s = Value::structure(mr);
    for (keel::usize j = 0; j < k; ++j) {
        keel::Array<Expr> colVec;
        colVec.reserve(tuples.size());
        for (const auto &t : tuples)
            if (j < t.size())
                colVec.push_back(t[j]);
        const keel::String vname = (c.kind(vars[j]) == NodeKind::Symbol)
                                       ? c.symbolName(vars[j]).clone()
                                       : keel::format("x{}", j + 1);
        s.field(vname) = fromSymVector(ctxPtr, colVec, /*column=*/true, mr);
    }
    outs[0] = keel::move(s);
}

numkit::Value symGroebner(keel::ArrayRef<numkit::Value> args,
                          keel::Allocator *mr)
{
    symGroebner_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    keel::Array<Expr> polys = toSymVector(args[0], c, "groebner");
    keel::Array<Expr> vars;
    if (args.size() >= 2) {
        vars = toSymVector(args[1], c, "groebner");
    } else {
        SymbolNameSet symSet;
        for (const auto &p : polys)
            collectSymbolsRec(c, p, symSet);
        for (const auto &nm : symSet)
            vars.push_back(c.symbol(nm));
    }
    MonomialOrder ord = MonomialOrder::Lex;
    if (args.size() >= 3 && (args[2].isChar() || args[2].isString())) {
        keel::String oStr = toLowerStr(trimStr(args[2].toString()));
        if (oStr.as_ref() == "grevlex" || oStr.as_ref() == "grlex")
            ord = MonomialOrder::GrevLex;
        else if (oStr.as_ref() == "lex")
            ord = MonomialOrder::Lex;
        else
            casFail("nk:groebner:invalidOrder",
                    "groebner: monomial order must be 'lex' or 'grevlex'");
    }
    GroebnerResult res = groebnerBasis(c, polys, vars, ord);
    if (!res.proved()) {
        casFail("nk:groebner:failed", keel::format("groebner: failed to compute Groebner basis ({})", res.reason));
    }
    return fromSymVector(ctxPtr, res.basis, /*column=*/false, mr);
}

numkit::Value symPolyReduce(keel::ArrayRef<numkit::Value> args,
                            keel::Allocator *mr)
{
    symPolyReduce_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    Expr f = toSymExpr(args[0], c, "polyreduce");
    keel::Array<Expr> G = toSymVector(args[1], c, "polyreduce");
    keel::Array<Expr> vars;
    if (args.size() >= 3) {
        vars = toSymVector(args[2], c, "polyreduce");
    } else {
        SymbolNameSet symSet;
        collectSymbolsRec(c, f, symSet);
        for (const auto &g : G)
            collectSymbolsRec(c, g, symSet);
        for (const auto &nm : symSet)
            vars.push_back(c.symbol(nm));
    }
    MonomialOrder ord = MonomialOrder::Lex;
    if (args.size() >= 4 && (args[3].isChar() || args[3].isString())) {
        keel::String oStr = toLowerStr(trimStr(args[3].toString()));
        if (oStr.as_ref() == "grevlex" || oStr.as_ref() == "grlex")
            ord = MonomialOrder::GrevLex;
    }
    Expr out = polyReduceMulti(c, f, G, vars, ord);
    if (out.isNull()) {
        casFail("nk:polyreduce:failed", "polyreduce: inputs must be polynomials in the specified variables");
    }
    return fromSymExpr(ctxPtr, out, mr);
}

namespace {

void symDsolve_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 1, 16, "dsolve");
}

void symPdsolve_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 4, 8, "pdsolve");
}

void symLaplace_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 1, 3, "laplace");
}

void symIlaplace_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 1, 3, "ilaplace");
}

void symFourier_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 1, 3, "fourier");
}

void symIfourier_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 1, 3, "ifourier");
}

void symZtrans_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 1, 3, "ztrans");
}

void symIztrans_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 1, 3, "iztrans");
}

void symRsolve_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 2, 4, "rsolve");
}

void symMatrixSquare_argcheck(const char *fn, const Value &A)
{
    if (!isSymValue(A) && !A.isNumeric() && !A.isLogical()) {
        casFail(keel::format("nk:{}:invalidType", fn),
                keel::format("{}: expected symbolic or numeric matrix", fn));
    }
    if (A.dims().rows() != A.dims().cols()) {
        casFail(keel::format("nk:{}:notSquare", fn),
                keel::format("{}: matrix must be square", fn));
    }
}

void symMatrixAny_argcheck(const char *fn, const Value &A)
{
    if (!isSymValue(A) && !A.isNumeric() && !A.isLogical()) {
        casFail(keel::format("nk:{}:invalidType", fn),
                keel::format("{}: expected symbolic or numeric matrix", fn));
    }
}

void symCharpoly_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 1, 2, "charpoly");
    symMatrixSquare_argcheck("charpoly", args[0]);
}

void symExpm_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 1, 2, "expm");
    symMatrixSquare_argcheck("expm", args[0]);
}

void symJacobian_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 1, 2, "jacobian");
}

void symGradient_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 1, 2, "gradient");
}

void symHessian_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 1, 2, "hessian");
}

void symLaplacian_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 1, 2, "laplacian");
}

void symWronskian_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 1, 2, "wronskian");
}

void symEulerLagrange_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 4, 5, "eulerlagrange");
}

void symHamiltonian_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 3, 3, "hamiltonian");
}

void symLegendreTransform_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 4, 4, "legendretransform");
}

void symPoissonBracket_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 4, 4, "poissonbracket");
}

void symLagrangeExtrema_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 2, 3, "lagrangeextrema");
}

void symFrenetSerret_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 1, 2, "frenetserret");
}

void symSurfaceCurvature_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 3, 3, "surfacecurvature");
}

void symGeodesic_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 2, 4, "geodesic");
}

void symLineIntegral_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 6, 6, "lineintegral");
}

void symSurfaceIntegral_argcheck(keel::ArrayRef<Value> args)
{
    argcheck::checkNargin(args.size(), 9, 9, "surfaceintegral");
}

bool exprMentionsSymbol(const Ctx &c, Expr e, Expr sym)
{
    if (e.isNull())
        return false;
    if (e == sym)
        return true;
    const keel::usize n = c.childCount(e);
    for (keel::usize i = 0; i < n; ++i)
        if (exprMentionsSymbol(c, c.child(e, i), sym))
            return true;
    return false;
}

bool extractLinearInSym(Ctx &c, Expr expr, Expr sym, Expr &coeffOut, Expr &restOut)
{
    Expr coeff = c.simplify(c.diff(expr, sym));
    if (exprMentionsSymbol(c, coeff, sym))
        return false;
    Expr rest = c.simplify(c.add({expr, c.neg(c.mul({coeff, sym}))}));
    if (exprMentionsSymbol(c, rest, sym))
        return false;
    coeffOut = coeff;
    restOut = rest;
    return true;
}

bool isSimpleIdentStr(keel::StringRef s)
{
    if (s.empty())
        return false;
    if (!keel::is_ascii_alpha(s[0]) && s[0] != '_')
        return false;
    for (keel::usize i = 1; i < s.size(); ++i)
        if (!keel::is_ascii_alnum(s[i]) && s[i] != '_')
            return false;
    return true;
}

keel::Array<keel::String> splitTopLevelCommas(keel::StringRef raw)
{
    keel::Array<keel::String> out;
    keel::i32 depth = 0;
    keel::usize start = 0;
    for (keel::usize i = 0; i < raw.size(); ++i) {
        const char ch = raw[i];
        if (ch == '(' || ch == '[' || ch == '{')
            ++depth;
        else if (ch == ')' || ch == ']' || ch == '}')
            --depth;
        else if (ch == ',' && depth == 0) {
            keel::String item = trimStr(raw.substr(start, i - start));
            if (!item.empty())
                out.push_back(keel::move(item));
            start = i + 1;
        }
    }
    keel::String tail = trimStr(raw.substr(start));
    if (!tail.empty())
        out.push_back(keel::move(tail));
    return out;
}

bool findTopLevelEq(keel::StringRef s, keel::usize &posOut, keel::usize &lenOut)
{
    keel::i32 depth = 0;
    for (keel::usize i = 0; i < s.size(); ++i) {
        if (s[i] == '(' || s[i] == '[')
            ++depth;
        else if (s[i] == ')' || s[i] == ']')
            --depth;
        else if (depth == 0 && s[i] == '=') {
            if (i > 0 && (s[i - 1] == '<' || s[i - 1] == '>' || s[i - 1] == '~' || s[i - 1] == '!'))
                continue;
            posOut = i;
            lenOut = (i + 1 < s.size() && s[i + 1] == '=') ? 2 : 1;
            return true;
        }
    }
    return false;
}

// Parse D<k?><dep> identifier: "Dy" -> (1, "y"), "D2y" -> (2, "y").
bool parseDerivIdent(keel::StringRef id, keel::i32 &orderOut, keel::String &depOut)
{
    if (id.size() < 2 || id[0] != 'D')
        return false;
    keel::usize pos = 1;
    keel::i32 ord = 0;
    while (pos < id.size() && keel::is_ascii_digit(id[pos])) {
        ord = ord * 10 + (id[pos] - '0');
        ++pos;
    }
    if (pos >= id.size())
        return false;
    keel::StringRef dep = id.substr(pos);
    if (!isSimpleIdentStr(dep))
        return false;
    if (pos == 1)
        ord = 1;
    if (ord < 1 || ord > 12)
        return false;
    orderOut = ord;
    depOut = keel::String::from(dep);
    return true;
}

struct ParsedDsolveIc {
    keel::i32 order = 0;
    Expr x0;
    Expr val;
};

bool tryParseIcClause(Ctx &c, keel::StringRef clause, keel::String &depOut, ParsedDsolveIc &icOut)
{
    keel::usize eqPos = 0, eqLen = 0;
    if (!findTopLevelEq(clause, eqPos, eqLen))
        return false;
    keel::String lhs = trimStr(clause.substr(0, eqPos));
    keel::String rhs = trimStr(clause.substr(eqPos + eqLen));
    if (lhs.empty() || rhs.empty() || lhs.back() != ')')
        return false;
    const keel::usize lp = lhs.as_ref().find('(');
    if (lp == keel::kInvalidIndex || lp == 0)
        return false;
    // Ensure '(' matches the final ')' at depth 0
    keel::i32 depth = 0;
    for (keel::usize i = lp; i < lhs.size(); ++i) {
        if (lhs[i] == '(') ++depth;
        else if (lhs[i] == ')') --depth;
        if (depth == 0 && i + 1 < lhs.size())
            return false;
    }
    keel::String head = trimStr(lhs.as_ref().substr(0, lp));
    keel::String argStr = trimStr(lhs.as_ref().substr(lp + 1, lhs.size() - lp - 2));
    if (!isSimpleIdentStr(head.as_ref()) || argStr.empty())
        return false;
    keel::i32 ord = 0;
    keel::String dep;
    if (parseDerivIdent(head.as_ref(), ord, dep)) {
        // Dy(0)=... or D2y(0)=...
    } else {
        ord = 0;
        dep = keel::move(head);
    }
    icOut.order = ord;
    icOut.x0 = parseExprFlexible(c, argStr, "dsolve");
    icOut.val = parseExprFlexible(c, rhs, "dsolve");
    if (depOut.empty())
        depOut = keel::move(dep);
    return true;
}

// Replace occurrences of `<dep>(<indep>)` in a string ODE with `<dep>`.
keel::String stripDepCallArg(keel::StringRef s, keel::StringRef dep, keel::StringRef indep)
{
    keel::String pattern = keel::format("{}({})", dep, indep);
    keel::String out;
    keel::usize pos = 0;
    while (pos < s.size()) {
        const keel::usize found = s.substr(pos).find(pattern.as_ref());
        if (found == keel::kInvalidIndex) {
            out.append(s.substr(pos));
            break;
        }
        const keel::usize absPos = pos + found;
        const bool prevIdent = (absPos > 0) && (keel::is_ascii_alnum(s[absPos - 1]) || s[absPos - 1] == '_');
        if (!prevIdent) {
            out.append(s.substr(pos, found));
            out.append(dep);
            pos = absPos + pattern.size();
        } else {
            out.append(s.substr(pos, found + 1));
            pos = absPos + 1;
        }
    }
    return out;
}

bool solveParsedOdeExpr(keel::Arc<Ctx> ctxPtr, Expr eq, keel::StringRef depName,
                        Expr xSym, keel::i32 maxOrder,
                        keel::ArrayRef<ParsedDsolveIc> ics,
                        keel::Allocator *mr, numkit::Value &outVal)
{
    Ctx &c = *ctxPtr;
    Expr ySym = c.symbol(depName);

    auto derivSym = [&](keel::i32 k) -> Expr {
        if (k == 0)
            return ySym;
        if (k == 1)
            return c.symbol(keel::format("D{}", depName));
        return c.symbol(keel::format("D{}{}", k, depName));
    };

    auto applyBoundaryIcs = [&](Expr generalSol) -> Expr {
        if (ics.empty())
            return generalSol;
        keel::Array<Expr> constVars;
        for (keel::i32 k = 1; k <= maxOrder; ++k) {
            Expr ck = c.symbol(keel::format("C{}", k));
            if (exprMentionsSymbol(c, generalSol, ck))
                constVars.push_back(ck);
        }
        if (constVars.empty() || ics.size() < constVars.size())
            return generalSol;
        keel::Array<Expr> icEqs;
        for (keel::usize i = 0; i < ics.size(); ++i) {
            Expr d = generalSol;
            for (keel::i32 k = 0; k < ics[i].order; ++k)
                d = c.diff(d, xSym);
            Expr atX0 = c.simplify(c.subs(d, xSym, ics[i].x0));
            icEqs.push_back(c.add({atX0, c.neg(ics[i].val)}));
        }
        auto sol = solveSystem(c, icEqs, constVars);
        if (sol.empty() || sol[0].size() != constVars.size())
            return generalSol;
        Expr res = generalSol;
        for (keel::usize i = 0; i < constVars.size(); ++i)
            res = c.subs(res, constVars[i], sol[0][i]);
        return c.simplify(res);
    };

    if (maxOrder == 1) {
        Expr a1, rest;
        if (!extractLinearInSym(c, eq, derivSym(1), a1, rest) || c.isZero(a1))
            casFail("nk:dsolve:failed", "dsolve: could not isolate 1st derivative");
        Expr rhs = c.simplify(c.neg(c.div(rest, a1)));
        OdeResult res;
        if (ics.size() == 1 && ics[0].order == 0) {
            res = dsolve1IVP(c, rhs, xSym, ySym, ics[0].x0, ics[0].val);
            if (!res.proved()) {
                OdeResult gen = dsolve1(c, rhs, xSym, ySym);
                if (gen.proved()) {
                    outVal = fromSymExpr(ctxPtr, applyBoundaryIcs(gen.y), mr);
                    return true;
                }
            }
        } else {
            res = dsolve1(c, rhs, xSym, ySym);
        }
        if (!res.proved())
            casFail("nk:dsolve:failed", keel::format("dsolve: could not solve 1st-order ODE ({})", res.reason));
        outVal = fromSymExpr(ctxPtr, res.y, mr);
        return true;
    }

    if (maxOrder == 2) {
        Expr a2, r2;
        if (!extractLinearInSym(c, eq, derivSym(2), a2, r2) || c.isZero(a2))
            casFail("nk:dsolve:failed", "dsolve: could not isolate 2nd derivative");
        Expr a1, r1, a0, r0;
        const bool isLin = extractLinearInSym(c, r2, derivSym(1), a1, r1) &&
                           extractLinearInSym(c, r1, ySym, a0, r0);
        if (isLin) {
            Expr f = c.simplify(c.neg(r0));
            bool hasSamePointIvp = false;
            Expr x0, y0, dy0;
            if (ics.size() == 2) {
                keel::i32 i0 = -1, i1 = -1;
                for (keel::i32 k = 0; k < 2; ++k) {
                    if (ics[k].order == 0) i0 = k;
                    else if (ics[k].order == 1) i1 = k;
                }
                if (i0 >= 0 && i1 >= 0 && c.isZero(c.simplify(c.add({ics[i0].x0, c.neg(ics[i1].x0)})))) {
                    hasSamePointIvp = true;
                    x0 = ics[i0].x0;
                    y0 = ics[i0].val;
                    dy0 = ics[i1].val;
                }
            }
            OdeResult res;
            if (hasSamePointIvp) {
                res = dsolve2LinearIVP(c, a2, a1, a0, f, xSym, x0, y0, dy0);
                if (!res.proved())
                    res = dsolve2EulerCauchyIVP(c, a2, a1, a0, f, xSym, x0, y0, dy0);
                if (!res.proved())
                    res = dsolve2SpecialIVP(c, a2, a1, a0, f, xSym, x0, y0, dy0);
                if (!res.proved()) {
                    keel::Array<Expr> cf = {a2, a1, a0};
                    keel::Array<Expr> iv = {y0, dy0};
                    res = dsolveNLinearIVP(c, cf, f, xSym, x0, iv);
                }
            } else {
                res = dsolve2Linear(c, a2, a1, a0, f, xSym);
                if (!res.proved())
                    res = dsolve2EulerCauchy(c, a2, a1, a0, f, xSym);
                if (!res.proved())
                    res = dsolve2Special(c, a2, a1, a0, f, xSym);
                if (!res.proved()) {
                    keel::Array<Expr> cf = {a2, a1, a0};
                    res = dsolveNLinear(c, cf, f, xSym);
                }
                if (res.proved() && !ics.empty())
                    res.y = applyBoundaryIcs(res.y);
            }
            if (!res.proved())
                casFail("nk:dsolve:failed", keel::format("dsolve: could not solve 2nd-order ODE ({})", res.reason));
            outVal = fromSymExpr(ctxPtr, res.y, mr);
            return true;
        }
        Expr dySym = derivSym(1);
        Expr rhs = c.simplify(c.neg(c.div(r2, a2)));
        OdeResult res;
        if (ics.size() == 2) {
            keel::i32 i0 = -1, i1 = -1;
            for (keel::i32 k = 0; k < 2; ++k) {
                if (ics[k].order == 0) i0 = k;
                else if (ics[k].order == 1) i1 = k;
            }
            if (i0 >= 0 && i1 >= 0)
                res = dsolve2NonlinearIVP(c, rhs, xSym, ySym, dySym, ics[i0].x0, ics[i0].val, ics[i1].val);
        }
        if (!res.proved())
            res = dsolve2Nonlinear(c, rhs, xSym, ySym, dySym);
        if (!res.proved())
            casFail("nk:dsolve:failed", keel::format("dsolve: could not solve 2nd-order nonlinear ODE ({})", res.reason));
        outVal = fromSymExpr(ctxPtr, res.y, mr);
        return true;
    }

    keel::Array<Expr> cf;
    cf.reserve(keel::as<keel::usize>(maxOrder + 1));
    Expr cur = eq;
    for (keel::i32 k = maxOrder; k >= 0; --k) {
        Expr ck, rk;
        if (!extractLinearInSym(c, cur, derivSym(k), ck, rk))
            casFail("nk:dsolve:failed", "dsolve: higher-order nonlinear ODE not supported");
        cf.push_back(ck);
        cur = rk;
    }
    Expr f = c.simplify(c.neg(cur));
    OdeResult res;
    if (keel::as<keel::i32>(ics.size()) == maxOrder) {
        keel::Array<Expr> initVals(keel::as<keel::usize>(maxOrder));
        keel::Array<bool> seen(keel::as<keel::usize>(maxOrder), false);
        bool sameX0 = true;
        Expr x0 = ics[0].x0;
        for (const auto &ic : ics) {
            if (ic.order < 0 || ic.order >= maxOrder || seen[keel::as<keel::usize>(ic.order)]) {
                sameX0 = false;
                break;
            }
            if (!c.isZero(c.simplify(c.add({ic.x0, c.neg(x0)})))) {
                sameX0 = false;
                break;
            }
            seen[keel::as<keel::usize>(ic.order)] = true;
            initVals[keel::as<keel::usize>(ic.order)] = ic.val;
        }
        if (sameX0)
            res = dsolveNLinearIVP(c, cf, f, xSym, x0, initVals);
    }
    if (!res.proved()) {
        res = dsolveNLinear(c, cf, f, xSym);
        if (res.proved() && !ics.empty())
            res.y = applyBoundaryIcs(res.y);
    }
    if (!res.proved())
        casFail("nk:dsolve:failed", keel::format("dsolve: N-th order ODE solve failed ({})", res.reason));
    outVal = fromSymExpr(ctxPtr, res.y, mr);
    return true;
}

bool trySolveStringDsolve(keel::Arc<Ctx> ctxPtr, keel::ArrayRef<numkit::Value> args,
                          keel::Allocator *mr, numkit::Value &outVal)
{
    if (args.empty() || !(args[0].isChar() || args[0].isString()))
        return false;
    bool hasEqArg = false;
    for (keel::usize i = 0; i < args.size(); ++i) {
        if (args[i].isChar() || args[i].isString()) {
            keel::usize p = 0, l = 0;
            if (findTopLevelEq(args[i].toString(), p, l)) {
                hasEqArg = true;
                break;
            }
        } else {
            return false;
        }
    }
    if (!hasEqArg)
        return false;

    Ctx &c = *ctxPtr;
    keel::usize nClauseArgs = args.size();
    keel::String indepName = keel::String::from("t");
    if (args.size() >= 2) {
        keel::String last = trimStr(args[args.size() - 1].toString());
        if (isSimpleIdentStr(last)) {
            indepName = keel::move(last);
            --nClauseArgs;
        }
    }

    keel::Array<keel::String> clauses;
    for (keel::usize i = 0; i < nClauseArgs; ++i) {
        auto parts = splitTopLevelCommas(args[i].toString());
        for (auto &p : parts)
            clauses.push_back(keel::move(p));
    }

    keel::Array<keel::String> odeClauses;
    keel::Array<ParsedDsolveIc> ics;
    keel::String depName;
    for (const auto &cl : clauses) {
        ParsedDsolveIc ic;
        if (tryParseIcClause(c, cl, depName, ic)) {
            ics.push_back(keel::move(ic));
        } else {
            odeClauses.push_back(cl.clone());
        }
    }
    if (odeClauses.size() != 1)
        return false;

    const keel::String &odeRaw = odeClauses[0];
    keel::i32 maxOrder = 0;
    for (keel::usize i = 0; i < odeRaw.size();) {
        if (keel::is_ascii_alpha(odeRaw[i]) || odeRaw[i] == '_') {
            keel::usize j = i + 1;
            while (j < odeRaw.size() && (keel::is_ascii_alnum(odeRaw[j]) || odeRaw[j] == '_'))
                ++j;
            keel::StringRef id = odeRaw.as_ref().substr(i, j - i);
            keel::i32 ord = 0;
            keel::String dep;
            if (parseDerivIdent(id, ord, dep)) {
                if (depName.empty() || dep == depName) {
                    depName = keel::move(dep);
                    if (ord > maxOrder)
                        maxOrder = ord;
                }
            }
            i = j;
        } else {
            ++i;
        }
    }
    if (depName.empty())
        depName = keel::String::from("y");
    if (maxOrder < 1)
        return false;

    keel::String odeNorm = stripDepCallArg(odeRaw, depName, indepName);
    Expr eq = parseExprFlexible(c, odeNorm, "dsolve");
    Expr xSym = c.symbol(indepName);
    return solveParsedOdeExpr(ctxPtr, eq, depName.as_ref(), xSym, maxOrder, ics.as_ref(), mr, outVal);
}

// Scan an expression tree for `diff(y(t), t [, n])` nodes to find (depName, indepSym, maxOrder).
void scanSymOdeDiffs(const Ctx &c, Expr e, keel::String &depName, Expr &indepSym, keel::i32 &maxOrder)
{
    if (e.isNull())
        return;
    if (c.kind(e) == NodeKind::Func && c.funcName(e) == "diff" &&
        (c.childCount(e) == 2 || c.childCount(e) == 3)) {
        const Expr target = c.child(e, 0);
        const Expr var = c.child(e, 1);
        if (c.kind(target) == NodeKind::Func && c.childCount(target) == 1 &&
            c.kind(var) == NodeKind::Symbol && c.child(target, 0) == var) {
            keel::i32 ord = 1;
            if (c.childCount(e) == 3 && c.kind(c.child(e, 2)) == NodeKind::Number) {
                keel::i64 k = 1;
                if (c.numberValue(c.child(e, 2)).fitsInt64(k))
                    ord = keel::as<keel::i32>(k);
            }
            if (depName.empty()) {
                depName = c.funcName(target).clone();
                indepSym = var;
            }
            if (c.funcName(target) == depName && var == indepSym && ord > maxOrder)
                maxOrder = ord;
            return;
        }
    }
    for (keel::usize i = 0; i < c.childCount(e); ++i)
        scanSymOdeDiffs(c, c.child(e, i), depName, indepSym, maxOrder);
}

// Replace `y(t)` -> `y`, `diff(y(t), t)` -> `Dy`, `diff(y(t), t, k)` -> `D<k>y`.
Expr replaceSymOdeFuncs(Ctx &c, Expr e, keel::StringRef depName, Expr indepSym)
{
    if (e.isNull())
        return e;
    const NodeKind k = c.kind(e);
    if (k == NodeKind::Func) {
        const keel::String &fn = c.funcName(e);
        if (fn == "diff" && (c.childCount(e) == 2 || c.childCount(e) == 3)) {
            const Expr target = c.child(e, 0);
            const Expr var = c.child(e, 1);
            if (c.kind(target) == NodeKind::Func && c.childCount(target) == 1 &&
                c.funcName(target) == depName && var == indepSym && c.child(target, 0) == indepSym) {
                keel::i32 ord = 1;
                if (c.childCount(e) == 3 && c.kind(c.child(e, 2)) == NodeKind::Number) {
                    keel::i64 kv = 1;
                    if (c.numberValue(c.child(e, 2)).fitsInt64(kv))
                        ord = keel::as<keel::i32>(kv);
                }
                if (ord == 1)
                    return c.symbol(keel::format("D{}", depName));
                return c.symbol(keel::format("D{}{}", ord, depName));
            }
        }
        if (fn == depName && c.childCount(e) == 1 && c.child(e, 0) == indepSym)
            return c.symbol(depName);
        keel::Array<Expr> kids;
        kids.reserve(c.childCount(e));
        for (keel::usize i = 0; i < c.childCount(e); ++i)
            kids.push_back(replaceSymOdeFuncs(c, c.child(e, i), depName, indepSym));
        return c.func(fn, kids);
    }
    if (k == NodeKind::Add || k == NodeKind::Mul) {
        keel::Array<Expr> kids;
        kids.reserve(c.childCount(e));
        for (keel::usize i = 0; i < c.childCount(e); ++i)
            kids.push_back(replaceSymOdeFuncs(c, c.child(e, i), depName, indepSym));
        return (k == NodeKind::Add) ? c.add(kids) : c.mul(kids);
    }
    if (k == NodeKind::Pow) {
        return c.pow(replaceSymOdeFuncs(c, c.child(e, 0), depName, indepSym),
                     replaceSymOdeFuncs(c, c.child(e, 1), depName, indepSym));
    }
    return e;
}

bool tryMatchSymIc(const Ctx &c, Expr eq, keel::StringRef depName, Expr indepSym, ParsedDsolveIc &icOut)
{
    if (c.kind(eq) != NodeKind::Func || c.funcName(eq) != "__eq" || c.childCount(eq) != 2)
        return false;
    auto matchSide = [&](Expr side, Expr other) -> bool {
        // y(x0) == val
        if (c.kind(side) == NodeKind::Func && c.funcName(side) == depName &&
            c.childCount(side) == 1 && c.child(side, 0) != indepSym) {
            icOut.order = 0;
            icOut.x0 = c.child(side, 0);
            icOut.val = other;
            return true;
        }
        // subs(diff(y(t), t [, k]), t, x0) == val (produced by Dy = diff(y, t); Dy(x0) == val)
        if (c.kind(side) == NodeKind::Func && c.funcName(side) == "subs" &&
            c.childCount(side) == 3) {
            const Expr inner = c.child(side, 0);
            const Expr var = c.child(side, 1);
            const Expr x0 = c.child(side, 2);
            if (var == indepSym && x0 != indepSym &&
                c.kind(inner) == NodeKind::Func && c.funcName(inner) == "diff" &&
                (c.childCount(inner) == 2 || c.childCount(inner) == 3) &&
                c.child(inner, 1) == indepSym) {
                const Expr target = c.child(inner, 0);
                if (c.kind(target) == NodeKind::Func && c.funcName(target) == depName &&
                    c.childCount(target) == 1 && c.child(target, 0) == indepSym) {
                    keel::i32 ord = 1;
                    if (c.childCount(inner) == 3 && c.kind(c.child(inner, 2)) == NodeKind::Number) {
                        keel::i64 kv = 1;
                        if (c.numberValue(c.child(inner, 2)).fitsInt64(kv))
                            ord = keel::as<keel::i32>(kv);
                    }
                    icOut.order = ord;
                    icOut.x0 = x0;
                    icOut.val = other;
                    return true;
                }
            }
        }
        // diff(y(x0), x0 [, k]) == val (fallback form)
        if (c.kind(side) == NodeKind::Func && c.funcName(side) == "diff" &&
            (c.childCount(side) == 2 || c.childCount(side) == 3)) {
            const Expr target = c.child(side, 0);
            const Expr x0 = c.child(side, 1);
            if (c.kind(target) == NodeKind::Func && c.funcName(target) == depName &&
                c.childCount(target) == 1 && x0 != indepSym) {
                keel::i32 ord = 1;
                if (c.childCount(side) == 3 && c.kind(c.child(side, 2)) == NodeKind::Number) {
                    keel::i64 kv = 1;
                    if (c.numberValue(c.child(side, 2)).fitsInt64(kv))
                        ord = keel::as<keel::i32>(kv);
                }
                icOut.order = ord;
                icOut.x0 = x0;
                icOut.val = other;
                return true;
            }
        }
        return false;
    };
    return matchSide(c.child(eq, 0), c.child(eq, 1)) || matchSide(c.child(eq, 1), c.child(eq, 0));
}

bool trySolveSymEqDsolve(keel::Arc<Ctx> ctxPtr, keel::ArrayRef<numkit::Value> args,
                         keel::Allocator *mr, numkit::Value &outVal)
{
    if (args.empty() || !isSymValue(args[0]))
        return false;
    Ctx &c = *ctxPtr;

    keel::Array<Expr> items;
    for (keel::usize i = 0; i < args.size(); ++i) {
        if (!isSymValue(args[i]))
            return false;
        keel::Array<Expr> part = toSymVector(args[i], c, "dsolve");
        for (const Expr e : part)
            items.push_back(e);
    }

    keel::String depName;
    Expr indepSym;
    keel::i32 maxOrder = 0;
    for (const Expr e : items)
        scanSymOdeDiffs(c, e, depName, indepSym, maxOrder);

    if (maxOrder < 1 || depName.empty() || indepSym.isNull())
        return false;

    keel::Array<Expr> odeEqs;
    keel::Array<ParsedDsolveIc> ics;
    for (const Expr e : items) {
        ParsedDsolveIc ic;
        if (tryMatchSymIc(c, e, depName.as_ref(), indepSym, ic)) {
            ics.push_back(keel::move(ic));
        } else {
            Expr norm = e;
            if (c.kind(norm) == NodeKind::Func && c.funcName(norm) == "__eq" && c.childCount(norm) == 2)
                norm = c.add({c.child(norm, 0), c.neg(c.child(norm, 1))});
            odeEqs.push_back(replaceSymOdeFuncs(c, norm, depName.as_ref(), indepSym));
        }
    }
    if (odeEqs.size() != 1)
        return false;

    return solveParsedOdeExpr(ctxPtr, odeEqs[0], depName.as_ref(), indepSym, maxOrder,
                              ics.as_ref(), mr, outVal);
}

} // namespace

numkit::Value symDsolve(keel::ArrayRef<numkit::Value> args,
                        keel::Allocator *mr)
{
    symDsolve_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;

    // 0a. Classic string-equation API: dsolve('Dy = -5*y', 'y(0)=1', 't')
    {
        numkit::Value strRes;
        if (trySolveStringDsolve(ctxPtr, args, mr, strRes))
            return strRes;
    }

    // 0b. Modern symbolic-equation API: dsolve(diff(y, t) == -5*y, y(0) == 1)
    {
        numkit::Value symRes;
        if (trySolveSymEqDsolve(ctxPtr, args, mr, symRes))
            return symRes;
    }

    // 1. First-order linear ODE system: dsolve(A, x) or dsolve(A, x, x0, y0)
    //    or inhomogeneous dsolve(A, f, x) / dsolve(A, f, x, x0, y0)
    if (args[0].dims().rows() > 1 && args[0].dims().cols() > 1) {
        SymMatrix A = toSymMatrix(args[0], c, "dsolve");
        if (args.size() == 2) {
            Expr x = toSymExpr(args[1], c, "dsolve");
            OdeSystemResult res = dsolveSystem1Linear(c, A, x);
            if (!res.proved())
                casFail("nk:dsolve:failed", keel::format("dsolve: linear system solve failed ({})", res.reason));
            return fromSymVector(ctxPtr, res.y, /*column=*/true, mr);
        }
        if (args.size() == 3) {
            keel::Array<Expr> f = toSymVector(args[1], c, "dsolve");
            Expr x = toSymExpr(args[2], c, "dsolve");
            OdeSystemResult res = dsolveSystem1Linear(c, A, f, x);
            if (!res.proved())
                casFail("nk:dsolve:failed", keel::format("dsolve: linear system solve failed ({})", res.reason));
            return fromSymVector(ctxPtr, res.y, /*column=*/true, mr);
        }
        if (args.size() == 4) {
            Expr x = toSymExpr(args[1], c, "dsolve");
            Expr x0 = toSymExpr(args[2], c, "dsolve");
            keel::Array<Expr> y0 = toSymVector(args[3], c, "dsolve");
            OdeSystemResult res = dsolveSystem1LinearIVP(c, A, x, x0, y0);
            if (!res.proved())
                casFail("nk:dsolve:failed", keel::format("dsolve: linear system IVP failed ({})", res.reason));
            return fromSymVector(ctxPtr, res.y, /*column=*/true, mr);
        }
        if (args.size() == 5) {
            keel::Array<Expr> f = toSymVector(args[1], c, "dsolve");
            Expr x = toSymExpr(args[2], c, "dsolve");
            Expr x0 = toSymExpr(args[3], c, "dsolve");
            keel::Array<Expr> y0 = toSymVector(args[4], c, "dsolve");
            OdeSystemResult res = dsolveSystem1LinearIVP(c, A, f, x, x0, y0);
            if (!res.proved())
                casFail("nk:dsolve:failed", keel::format("dsolve: linear system IVP failed ({})", res.reason));
            return fromSymVector(ctxPtr, res.y, /*column=*/true, mr);
        }
    }

    // 2. N-th order constant-coefficient linear ODE: dsolve(coeffs_vec, f, x, [x0, initVals])
    if ((isSymValue(args[0]) || args[0].isNumeric()) && args[0].numel() > 1 && args.size() >= 3) {
        keel::Array<Expr> cf = toSymVector(args[0], c, "dsolve");
        Expr f = toSymExpr(args[1], c, "dsolve");
        Expr x = toSymExpr(args[2], c, "dsolve");
        OdeResult res;
        if (args.size() >= 5) {
            Expr x0 = toSymExpr(args[3], c, "dsolve");
            keel::Array<Expr> initVals = toSymVector(args[4], c, "dsolve");
            res = dsolveNLinearIVP(c, cf, f, x, x0, initVals);
        } else {
            res = dsolveNLinear(c, cf, f, x);
        }
        if (!res.proved())
            casFail("nk:dsolve:failed", keel::format("dsolve: N-th order ODE solve failed ({})", res.reason));
        return fromSymExpr(ctxPtr, res.y, mr);
    }

    // 3. 1st-order ODE: dsolve(rhs, [x, y]) or dsolve(rhs, x, y, x0, y0)
    if (args.size() <= 3) {
        Expr rhs = toSymExpr(args[0], c, "dsolve");
        Expr x = (args.size() >= 2) ? toSymExpr(args[1], c, "dsolve") : c.symbol("x");
        Expr y = (args.size() >= 3) ? toSymExpr(args[2], c, "dsolve") : c.symbol("y");
        OdeResult res = dsolve1(c, rhs, x, y);
        if (!res.proved())
            casFail("nk:dsolve:failed", keel::format("dsolve: could not solve 1st-order ODE ({})", res.reason));
        return fromSymExpr(ctxPtr, res.y, mr);
    }
    if (args.size() == 5 && args[3].isChar() == false) {
        // Distinguish 1st-order IVP (rhs, x, y, x0, y0) vs 2nd-order linear (a, b, d, f, x):
        // In 2nd-order linear (a, b, d, f, x), arg[4] is a symbol `x` and arg[1], arg[2] are coefficients (not y).
        Expr a3 = toSymExpr(args[3], c, "dsolve");
        Expr a4 = toSymExpr(args[4], c, "dsolve");
        Expr a2 = toSymExpr(args[2], c, "dsolve");
        if (c.kind(a2) == NodeKind::Symbol && c.symbolName(a2).as_ref() == "y"
            && !(c.kind(a4) == NodeKind::Symbol && c.symbolName(a4).as_ref() == "x")) {
            Expr rhs = toSymExpr(args[0], c, "dsolve");
            Expr x = toSymExpr(args[1], c, "dsolve");
            OdeResult res = dsolve1IVP(c, rhs, x, a2, a3, a4);
            if (res.proved())
                return fromSymExpr(ctxPtr, res.y, mr);
        }
        // 2nd-order ODE: a*y'' + b*y' + d*y = f(x)
        Expr a = toSymExpr(args[0], c, "dsolve");
        Expr b = toSymExpr(args[1], c, "dsolve");
        Expr d = a2;
        Expr f = a3;
        Expr x = a4;
        OdeResult res = dsolve2Linear(c, a, b, d, f, x);
        if (!res.proved())
            res = dsolve2EulerCauchy(c, a, b, d, f, x);
        if (!res.proved())
            res = dsolve2Special(c, a, b, d, f, x);
        if (!res.proved())
            casFail("nk:dsolve:failed", keel::format("dsolve: could not solve 2nd-order ODE ({})", res.reason));
        return fromSymExpr(ctxPtr, res.y, mr);
    }
    if (args.size() == 4) {
        // 2nd-order nonlinear ODE: y'' = rhs(x, y, dy), args = (rhs, x, y, dy)
        Expr rhs = toSymExpr(args[0], c, "dsolve");
        Expr x = toSymExpr(args[1], c, "dsolve");
        Expr y = toSymExpr(args[2], c, "dsolve");
        Expr dy = toSymExpr(args[3], c, "dsolve");
        OdeResult res = dsolve2Nonlinear(c, rhs, x, y, dy);
        if (!res.proved())
            casFail("nk:dsolve:failed", keel::format("dsolve: could not solve 2nd-order nonlinear ODE ({})", res.reason));
        return fromSymExpr(ctxPtr, res.y, mr);
    }
    if (args.size() == 7) {
        // 2nd-order nonlinear IVP: (rhs, x, y, dy, x0, y0, dy0)
        Expr rhs = toSymExpr(args[0], c, "dsolve");
        Expr x = toSymExpr(args[1], c, "dsolve");
        Expr y = toSymExpr(args[2], c, "dsolve");
        Expr dy = toSymExpr(args[3], c, "dsolve");
        Expr x0 = toSymExpr(args[4], c, "dsolve");
        Expr y0 = toSymExpr(args[5], c, "dsolve");
        Expr dy0 = toSymExpr(args[6], c, "dsolve");
        OdeResult res = dsolve2NonlinearIVP(c, rhs, x, y, dy, x0, y0, dy0);
        if (!res.proved())
            casFail("nk:dsolve:failed", keel::format("dsolve: 2nd-order nonlinear IVP failed ({})", res.reason));
        return fromSymExpr(ctxPtr, res.y, mr);
    }
    if (args.size() == 8) {
        // 2nd-order linear IVP: (a, b, d, f, x, x0, y0, dy0)
        Expr a = toSymExpr(args[0], c, "dsolve");
        Expr b = toSymExpr(args[1], c, "dsolve");
        Expr d = toSymExpr(args[2], c, "dsolve");
        Expr f = toSymExpr(args[3], c, "dsolve");
        Expr x = toSymExpr(args[4], c, "dsolve");
        Expr x0 = toSymExpr(args[5], c, "dsolve");
        Expr y0 = toSymExpr(args[6], c, "dsolve");
        Expr dy0 = toSymExpr(args[7], c, "dsolve");
        OdeResult res = dsolve2LinearIVP(c, a, b, d, f, x, x0, y0, dy0);
        if (!res.proved())
            res = dsolve2EulerCauchyIVP(c, a, b, d, f, x, x0, y0, dy0);
        if (!res.proved())
            res = dsolve2SpecialIVP(c, a, b, d, f, x, x0, y0, dy0);
        if (!res.proved())
            casFail("nk:dsolve:failed", keel::format("dsolve: 2nd-order IVP failed ({})", res.reason));
        return fromSymExpr(ctxPtr, res.y, mr);
    }
    casFail("nk:dsolve:invalidArgs", "dsolve: unsupported argument count");
}

numkit::Value symPdsolve(keel::ArrayRef<numkit::Value> args,
                         keel::Allocator *mr)
{
    symPdsolve_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;

    if (args[0].isChar() || args[0].isString()) {
        keel::String kind = toLowerStr(trimStr(args[0].toString()));
        if (kind.as_ref() == "wave") {
            Expr cWave = toSymExpr(args[1], c, "pdsolve");
            Expr x = toSymExpr(args[2], c, "pdsolve");
            Expr t = toSymExpr(args[3], c, "pdsolve");
            Expr phi = (args.size() >= 5) ? toSymExpr(args[4], c, "pdsolve") : Expr{};
            Expr psi = (args.size() >= 6) ? toSymExpr(args[5], c, "pdsolve") : Expr{};
            Expr forcing = (args.size() >= 7) ? toSymExpr(args[6], c, "pdsolve") : Expr{};
            PdeResult res = pdsolveWaveDalembert(c, cWave, x, t, phi, psi, forcing);
            if (!res.proved())
                casFail("nk:pdsolve:failed", keel::format("pdsolve: wave PDE solve failed ({})", res.reason));
            return fromSymExpr(ctxPtr, res.u, mr);
        }
        if (kind.as_ref() == "heat") {
            if (args.size() < 6)
                casFail("nk:pdsolve:tooFewArgs", "pdsolve('heat', alpha, L, initU, x, t): expected at least 6 arguments");
            Expr alpha = toSymExpr(args[1], c, "pdsolve");
            Expr L = toSymExpr(args[2], c, "pdsolve");
            Expr initU = toSymExpr(args[3], c, "pdsolve");
            Expr x = toSymExpr(args[4], c, "pdsolve");
            Expr t = toSymExpr(args[5], c, "pdsolve");
            PdeBoundaryKind bc = PdeBoundaryKind::Dirichlet;
            if (args.size() >= 7 && (args[6].isChar() || args[6].isString())) {
                keel::String bStr = toLowerStr(trimStr(args[6].toString()));
                if (bStr.as_ref() == "neumann")
                    bc = PdeBoundaryKind::Neumann;
            }
            keel::i32 maxModes = (args.size() >= 8) ? keel::as<keel::i32>(args[7].toScalar()) : 5;
            PdeResult res = pdsolveHeat1D(c, alpha, L, initU, x, t, bc, maxModes);
            if (!res.proved())
                casFail("nk:pdsolve:failed", keel::format("pdsolve: heat PDE solve failed ({})", res.reason));
            return fromSymExpr(ctxPtr, res.u, mr);
        }
    }

    if (args.size() >= 6) {
        Expr a = toSymExpr(args[0], c, "pdsolve");
        Expr b = toSymExpr(args[1], c, "pdsolve");
        Expr rhs = toSymExpr(args[2], c, "pdsolve");
        Expr x = toSymExpr(args[3], c, "pdsolve");
        Expr y = toSymExpr(args[4], c, "pdsolve");
        Expr u = toSymExpr(args[5], c, "pdsolve");
        PdeResult res = pdsolve1Quasilinear(c, a, b, rhs, x, y, u);
        if (!res.proved())
            casFail("nk:pdsolve:failed", keel::format("pdsolve: 1st-order PDE solve failed ({})", res.reason));
        return fromSymExpr(ctxPtr, res.u, mr);
    }
    casFail("nk:pdsolve:invalidArgs", "pdsolve: unsupported PDE signature");
}

namespace {

bool containsAbstractFuncRec(const Ctx &c, Expr e)
{
    if (e.isNull())
        return false;
    if (c.kind(e) == NodeKind::Func) {
        const keel::String &fn = c.funcName(e);
        if (fn == "diff" || fn == "laplace" || fn == "ilaplace")
            return true;
        const bool isBuiltin =
            fn == "__eq" || fn == "__ne" || fn == "__lt" || fn == "__le" || fn == "__gt" || fn == "__ge" ||
            fn == "exp" || fn == "log" || fn == "sqrt" || fn == "abs" || fn == "sign" ||
            fn == "sin" || fn == "cos" || fn == "tan" || fn == "asin" || fn == "acos" || fn == "atan" ||
            fn == "sinh" || fn == "cosh" || fn == "tanh" || fn == "asinh" || fn == "acosh" || fn == "atanh" ||
            fn == "erf" || fn == "erfc" || fn == "erfi" || fn == "gamma" || fn == "heaviside" ||
            fn == "dirac" || fn == "zeta" || fn == "Ei";
        if (!isBuiltin)
            return true;
    }
    for (keel::usize i = 0; i < c.childCount(e); ++i) {
        if (containsAbstractFuncRec(c, c.child(e, i)))
            return true;
    }
    return false;
}

bool exprHasSymbolRec(const Ctx &c, Expr e, Expr sym)
{
    if (e == sym)
        return true;
    for (keel::usize i = 0; i < c.childCount(e); ++i) {
        if (exprHasSymbolRec(c, c.child(e, i), sym))
            return true;
    }
    return false;
}

Expr laplaceWithAbstractFallback(Ctx &c, Expr f, Expr t, Expr s)
{
    LaplaceResult res = laplace(c, f, t, s);
    if (res.proved())
        return res.F;
    if (c.kind(f) == NodeKind::Func && c.funcName(f) == "__eq" && c.childCount(f) == 2) {
        return c.func("__eq",
                      laplaceWithAbstractFallback(c, c.child(f, 0), t, s),
                      laplaceWithAbstractFallback(c, c.child(f, 1), t, s));
    }
    if (c.kind(f) == NodeKind::Add) {
        keel::Array<Expr> parts;
        parts.reserve(c.childCount(f));
        for (keel::usize i = 0; i < c.childCount(f); ++i)
            parts.push_back(laplaceWithAbstractFallback(c, c.child(f, i), t, s));
        return c.add(parts);
    }
    if (c.kind(f) == NodeKind::Mul) {
        keel::Array<Expr> freeFactors;
        keel::Array<Expr> depFactors;
        for (keel::usize i = 0; i < c.childCount(f); ++i) {
            const Expr ch = c.child(f, i);
            if (!exprHasSymbolRec(c, ch, t))
                freeFactors.push_back(ch);
            else
                depFactors.push_back(ch);
        }
        if (!freeFactors.empty() && !depFactors.empty()) {
            const Expr dep = (depFactors.size() == 1) ? depFactors[0] : c.mul(depFactors);
            freeFactors.push_back(laplaceWithAbstractFallback(c, dep, t, s));
            return c.mul(freeFactors);
        }
    }
    return c.func("laplace", {f, t, s});
}

} // namespace

numkit::Value symLaplace(keel::ArrayRef<numkit::Value> args,
                         keel::Allocator *mr)
{
    symLaplace_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    Expr f = toSymExpr(args[0], c, "laplace");
    Expr t = (args.size() >= 2) ? toSymExpr(args[1], c, "laplace") : defaultSymVar(c, args[0], "t");
    Expr s = (args.size() >= 3) ? toSymExpr(args[2], c, "laplace") : c.symbol("s");
    LaplaceResult res = laplace(c, f, t, s);
    if (res.proved())
        return fromSymExpr(ctxPtr, res.F, mr);
    if (containsAbstractFuncRec(c, f))
        return fromSymExpr(ctxPtr, laplaceWithAbstractFallback(c, f, t, s), mr);
    casFail("nk:laplace:unevaluated", keel::format("laplace: could not compute Laplace transform ({})", res.reason));
}

numkit::Value symIlaplace(keel::ArrayRef<numkit::Value> args,
                          keel::Allocator *mr)
{
    symIlaplace_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    Expr F = toSymExpr(args[0], c, "ilaplace");
    Expr s = (args.size() >= 2) ? toSymExpr(args[1], c, "ilaplace") : defaultSymVar(c, args[0], "s");
    Expr t = (args.size() >= 3) ? toSymExpr(args[2], c, "ilaplace") : c.symbol("t");
    LaplaceResult res = ilaplace(c, F, s, t);
    if (res.proved())
        return fromSymExpr(ctxPtr, res.F, mr);
    if (containsAbstractFuncRec(c, F))
        return fromSymExpr(ctxPtr, c.func("ilaplace", {F, s, t}), mr);
    casFail("nk:ilaplace:unevaluated", keel::format("ilaplace: could not compute inverse Laplace transform ({})", res.reason));
}

numkit::Value symFourier(keel::ArrayRef<numkit::Value> args,
                         keel::Allocator *mr)
{
    symFourier_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    Expr f = toSymExpr(args[0], c, "fourier");
    Expr t = (args.size() >= 2) ? toSymExpr(args[1], c, "fourier") : defaultSymVar(c, args[0], "t");
    Expr w = (args.size() >= 3) ? toSymExpr(args[2], c, "fourier") : c.symbol("w");
    FourierResult res = fourier(c, f, t, w);
    if (!res.proved())
        casFail("nk:fourier:unevaluated", keel::format("fourier: could not compute Fourier transform ({})", res.reason));
    return fromSymExpr(ctxPtr, res.F, mr);
}

numkit::Value symIfourier(keel::ArrayRef<numkit::Value> args,
                          keel::Allocator *mr)
{
    symIfourier_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    Expr F = toSymExpr(args[0], c, "ifourier");
    Expr w = (args.size() >= 2) ? toSymExpr(args[1], c, "ifourier") : defaultSymVar(c, args[0], "w");
    Expr t = (args.size() >= 3) ? toSymExpr(args[2], c, "ifourier") : c.symbol("t");
    FourierResult res = ifourier(c, F, w, t);
    if (!res.proved())
        casFail("nk:ifourier:unevaluated", keel::format("ifourier: could not compute inverse Fourier transform ({})", res.reason));
    return fromSymExpr(ctxPtr, res.F, mr);
}

numkit::Value symZtrans(keel::ArrayRef<numkit::Value> args,
                        keel::Allocator *mr)
{
    symZtrans_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    Expr f = toSymExpr(args[0], c, "ztrans");
    Expr n = (args.size() >= 2) ? toSymExpr(args[1], c, "ztrans") : defaultSymVar(c, args[0], "n");
    Expr z = (args.size() >= 3) ? toSymExpr(args[2], c, "ztrans") : c.symbol("z");
    ZTransResult res = ztrans(c, f, n, z);
    if (!res.proved())
        casFail("nk:ztrans:unevaluated", keel::format("ztrans: could not compute Z-transform ({})", res.reason));
    return fromSymExpr(ctxPtr, res.F, mr);
}

numkit::Value symIztrans(keel::ArrayRef<numkit::Value> args,
                         keel::Allocator *mr)
{
    symIztrans_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    Expr F = toSymExpr(args[0], c, "iztrans");
    Expr z = (args.size() >= 2) ? toSymExpr(args[1], c, "iztrans") : defaultSymVar(c, args[0], "z");
    Expr n = (args.size() >= 3) ? toSymExpr(args[2], c, "iztrans") : c.symbol("n");
    ZTransResult res = iztrans(c, F, z, n);
    if (!res.proved())
        casFail("nk:iztrans:unevaluated", keel::format("iztrans: could not compute inverse Z-transform ({})", res.reason));
    return fromSymExpr(ctxPtr, res.F, mr);
}

numkit::Value symRsolve(keel::ArrayRef<numkit::Value> args,
                        keel::Allocator *mr)
{
    symRsolve_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    keel::Array<Expr> cf = toSymVector(args[0], c, "rsolve");
    Expr rhs = toSymExpr(args[1], c, "rsolve");
    Expr n = (args.size() >= 3) ? toSymExpr(args[2], c, "rsolve") : c.symbol("n");
    RsolveResult res;
    if (args.size() >= 4) {
        keel::Array<Expr> initVals = toSymVector(args[3], c, "rsolve");
        res = rsolveIVP(c, cf, rhs, n, initVals);
    } else {
        res = rsolve(c, cf, rhs, n);
    }
    if (!res.proved())
        casFail("nk:rsolve:failed", keel::format("rsolve: could not solve recurrence ({})", res.reason));
    return fromSymExpr(ctxPtr, res.y, mr);
}

numkit::Value symDet(const numkit::Value &A,
                     keel::Allocator *mr)
{
    symMatrixSquare_argcheck("det", A);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    SymMatrix M = toSymMatrix(A, c, "det");
    return fromSymExpr(ctxPtr, det(c, M), mr);
}

numkit::Value symInv(const numkit::Value &A,
                     keel::Allocator *mr)
{
    symMatrixSquare_argcheck("inv", A);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    SymMatrix M = toSymMatrix(A, c, "inv");
    SymMatrix Minv = inv(c, M);
    if (Minv.empty() && !M.empty()) {
        casFail("nk:inv:singular", "inv: symbolic matrix is singular");
    }
    return fromSymMatrix(ctxPtr, Minv, mr);
}

numkit::Value symTrace(const numkit::Value &A,
                       keel::Allocator *mr)
{
    symMatrixSquare_argcheck("trace", A);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    SymMatrix M = toSymMatrix(A, c, "trace");
    return fromSymExpr(ctxPtr, M.trace(c), mr);
}

numkit::Value symAdjugate(const numkit::Value &A,
                          keel::Allocator *mr)
{
    symMatrixSquare_argcheck("adjugate", A);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    SymMatrix M = toSymMatrix(A, c, "adjugate");
    return fromSymMatrix(ctxPtr, adjugate(c, M), mr);
}

numkit::Value symCharpoly(keel::ArrayRef<numkit::Value> args,
                          keel::Allocator *mr)
{
    symCharpoly_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    SymMatrix M = toSymMatrix(args[0], c, "charpoly");
    if (args.size() >= 2) {
        Expr lam = toSymExpr(args[1], c, "charpoly");
        return fromSymExpr(ctxPtr, charpoly(c, M, lam), mr);
    }
    Expr lam = c.symbol("__lambda_cp");
    Expr cp = charpoly(c, M, lam);
    PolyCoeffsResult res = coeffs(c, cp, lam);
    keel::Array<Expr> desc;
    desc.reserve(res.dense.size());
    for (keel::usize i = res.dense.size(); i-- > 0;)
        desc.push_back(res.dense[i]);
    return fromSymVector(ctxPtr, desc, /*column=*/false, mr);
}

numkit::Value symRank(const numkit::Value &A,
                      keel::Allocator *mr)
{
    symMatrixAny_argcheck("rank", A);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    SymMatrix M = toSymMatrix(A, c, "rank");
    return Value::scalar(keel::as<keel::f64>(rank(c, M)), mr);
}

void symRref(const numkit::Value &A, keel::usize nargout,
             keel::MutArrayRef<numkit::Value> outs,
             keel::Allocator *mr)
{
    symMatrixAny_argcheck("rref", A);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    SymMatrix M = toSymMatrix(A, c, "rref");
    keel::Array<keel::usize> pivots;
    SymMatrix R = rref(c, M, &pivots);
    outs[0] = fromSymMatrix(ctxPtr, R, mr);
    if (nargout >= 2 && outs.size() >= 2) {
        Value jb = Value::matrix(1, pivots.size(), ValueType::DOUBLE, mr);
        keel::f64 *jp = jb.doubleDataMut();
        for (keel::usize i = 0; i < pivots.size(); ++i)
            jp[i] = keel::as<keel::f64>(pivots[i] + 1);
        outs[1] = keel::move(jb);
    }
}

numkit::Value symNull(const numkit::Value &A,
                      keel::Allocator *mr)
{
    symMatrixAny_argcheck("null", A);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    SymMatrix M = toSymMatrix(A, c, "null");
    keel::Array<SymMatrix> basis = nullspace(c, M);
    if (basis.empty()) {
        return fromSymMatrix(ctxPtr, SymMatrix(M.cols(), 0), mr);
    }
    SymMatrix Z(M.cols(), basis.size(), c.zero());
    for (keel::usize col = 0; col < basis.size(); ++col) {
        for (keel::usize r = 0; r < M.cols(); ++r)
            Z(r, col) = basis[col](r, 0);
    }
    return fromSymMatrix(ctxPtr, Z, mr);
}

numkit::Value symLinsolve(const numkit::Value &A, const numkit::Value &B,
                          keel::Allocator *mr)
{
    symMatrixAny_argcheck("linsolve", A);
    symMatrixAny_argcheck("linsolve", B);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    SymMatrix MA = toSymMatrix(A, c, "linsolve");
    SymMatrix MB = toSymMatrix(B, c, "linsolve");
    if (MA.rows() != MB.rows()) {
        casFail("nk:linsolve:dimMismatch", "linsolve: A and B must have the same number of rows");
    }
    SymMatrix X = linsolve(c, MA, MB);
    if (X.empty() && !MA.empty()) {
        casFail("nk:linsolve:singular", "linsolve: symbolic linear system is singular or inconsistent");
    }
    return fromSymMatrix(ctxPtr, X, mr);
}

void symLu(const numkit::Value &A, keel::usize nargout,
           keel::MutArrayRef<numkit::Value> outs,
           keel::Allocator *mr)
{
    symMatrixAny_argcheck("lu", A);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    SymMatrix M = toSymMatrix(A, c, "lu");
    LUDecomposition res = lu(c, M);
    if (!res.proved()) {
        casFail("nk:lu:failed", keel::format("lu: symbolic LU decomposition failed ({})", res.reason));
    }
    if (nargout <= 2) {
        outs[0] = fromSymMatrix(ctxPtr, res.P.transpose().mul(c, res.L), mr);
        if (nargout >= 2 && outs.size() >= 2)
            outs[1] = fromSymMatrix(ctxPtr, res.U, mr);
    } else {
        outs[0] = fromSymMatrix(ctxPtr, res.L, mr);
        outs[1] = fromSymMatrix(ctxPtr, res.U, mr);
        outs[2] = fromSymMatrix(ctxPtr, res.P, mr);
    }
}

void symQr(const numkit::Value &A, keel::usize nargout,
           keel::MutArrayRef<numkit::Value> outs,
           keel::Allocator *mr)
{
    symMatrixAny_argcheck("qr", A);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    SymMatrix M = toSymMatrix(A, c, "qr");
    QRDecomposition res = qr(c, M);
    if (!res.proved()) {
        casFail("nk:qr:failed", keel::format("qr: symbolic QR decomposition failed ({})", res.reason));
    }
    outs[0] = fromSymMatrix(ctxPtr, res.Q, mr);
    if (nargout >= 2 && outs.size() >= 2)
        outs[1] = fromSymMatrix(ctxPtr, res.R, mr);
}

void symEig(const numkit::Value &A, keel::usize nargout,
            keel::MutArrayRef<numkit::Value> outs,
            keel::Allocator *mr)
{
    symMatrixSquare_argcheck("eig", A);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    SymMatrix M = toSymMatrix(A, c, "eig");
    if (nargout <= 1) {
        keel::Array<Expr> vals = eigenvalues(c, M);
        outs[0] = fromSymVector(ctxPtr, vals, /*column=*/true, mr);
        return;
    }
    keel::Array<EigenPair> pairs = eigenvectors(c, M);
    keel::Array<Expr> diagVals;
    keel::Array<SymMatrix> cols;
    for (const auto &ep : pairs) {
        if (!ep.vectors.empty()) {
            for (const auto &v : ep.vectors) {
                diagVals.push_back(ep.lambda);
                cols.push_back(v);
            }
        } else {
            for (keel::usize m = 0; m < ep.multiplicity; ++m)
                diagVals.push_back(ep.lambda);
        }
    }
    const keel::usize n = M.rows();
    SymMatrix V(n, cols.size(), c.zero());
    for (keel::usize j = 0; j < cols.size(); ++j)
        for (keel::usize r = 0; r < n; ++r)
            V(r, j) = cols[j](r, 0);
    SymMatrix D = SymMatrix::diag(c, diagVals);
    outs[0] = fromSymMatrix(ctxPtr, V, mr);
    if (outs.size() >= 2)
        outs[1] = fromSymMatrix(ctxPtr, D, mr);
}

void symJordan(const numkit::Value &A, keel::usize nargout,
               keel::MutArrayRef<numkit::Value> outs,
               keel::Allocator *mr)
{
    symMatrixSquare_argcheck("jordan", A);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    SymMatrix M = toSymMatrix(A, c, "jordan");
    JordanDecomposition res = jordanForm(c, M);
    if (!res.proved()) {
        casFail("nk:jordan:failed", keel::format("jordan: Jordan canonical form failed ({})", res.reason));
    }
    if (nargout <= 1) {
        outs[0] = fromSymMatrix(ctxPtr, res.J, mr);
    } else {
        outs[0] = fromSymMatrix(ctxPtr, res.P, mr);
        outs[1] = fromSymMatrix(ctxPtr, res.J, mr);
        if (nargout >= 3 && outs.size() >= 3)
            outs[2] = fromSymMatrix(ctxPtr, res.PInv, mr);
    }
}

numkit::Value symExpm(keel::ArrayRef<numkit::Value> args,
                      keel::Allocator *mr)
{
    symExpm_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    SymMatrix M = toSymMatrix(args[0], c, "expm");
    if (args.size() >= 2) {
        Expr t = toSymExpr(args[1], c, "expm");
        SymMatrix Phi = matrixExp(c, M, t);
        if (Phi.empty() && !M.empty())
            casFail("nk:expm:failed", "expm: symbolic matrix exponential failed");
        return fromSymMatrix(ctxPtr, Phi, mr);
    }
    Expr t = c.symbol("__t_expm");
    SymMatrix Phi = matrixExp(c, M, t);
    if (Phi.empty() && !M.empty())
        casFail("nk:expm:failed", "expm: symbolic matrix exponential failed");
    return fromSymMatrix(ctxPtr, Phi.subs(c, t, c.one()), mr);
}

numkit::Value symJacobian(keel::ArrayRef<numkit::Value> args,
                          keel::Allocator *mr)
{
    symJacobian_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    keel::Array<Expr> funcs = toSymVector(args[0], c, "jacobian");
    keel::Array<Expr> vars;
    if (args.size() >= 2) {
        vars = toSymVector(args[1], c, "jacobian");
    } else {
        SymbolNameSet symSet;
        for (const auto &f : funcs)
            collectSymbolsRec(c, f, symSet);
        for (const auto &nm : symSet)
            vars.push_back(c.symbol(nm));
        if (vars.empty())
            vars.push_back(c.symbol("x"));
    }
    return fromSymMatrix(ctxPtr, jacobian(c, funcs, vars), mr);
}

numkit::Value symGradient(keel::ArrayRef<numkit::Value> args,
                          keel::Allocator *mr)
{
    symGradient_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    Expr f = toSymExpr(args[0], c, "gradient");
    keel::Array<Expr> vars;
    if (args.size() >= 2) {
        vars = toSymVector(args[1], c, "gradient");
    } else {
        SymbolNameSet symSet;
        collectSymbolsRec(c, f, symSet);
        for (const auto &nm : symSet)
            vars.push_back(c.symbol(nm));
        if (vars.empty())
            vars.push_back(c.symbol("x"));
    }
    return fromSymMatrix(ctxPtr, gradient(c, f, vars), mr);
}

numkit::Value symHessian(keel::ArrayRef<numkit::Value> args,
                         keel::Allocator *mr)
{
    symHessian_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    Expr f = toSymExpr(args[0], c, "hessian");
    keel::Array<Expr> vars;
    if (args.size() >= 2) {
        vars = toSymVector(args[1], c, "hessian");
    } else {
        SymbolNameSet symSet;
        collectSymbolsRec(c, f, symSet);
        for (const auto &nm : symSet)
            vars.push_back(c.symbol(nm));
        if (vars.empty())
            vars.push_back(c.symbol("x"));
    }
    return fromSymMatrix(ctxPtr, hessian(c, f, vars), mr);
}

numkit::Value symDivergence(const numkit::Value &F, const numkit::Value &vars,
                            keel::Allocator *mr)
{
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    keel::Array<Expr> fVec = toSymVector(F, c, "divergence");
    keel::Array<Expr> vVec = toSymVector(vars, c, "divergence");
    if (fVec.size() != vVec.size() || fVec.empty()) {
        casFail("nk:divergence:dimMismatch",
                "divergence: vector field F and coordinate vector vars must have the same non-zero length");
    }
    return fromSymExpr(ctxPtr, divergence(c, fVec, vVec), mr);
}

numkit::Value symCurl(const numkit::Value &F, const numkit::Value &vars,
                      keel::Allocator *mr)
{
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    keel::Array<Expr> fVec = toSymVector(F, c, "curl");
    keel::Array<Expr> vVec = toSymVector(vars, c, "curl");
    if (fVec.size() != 3 || vVec.size() != 3) {
        casFail("nk:curl:expected3D",
                "curl: vector field F and coordinate vector vars must have 3 components");
    }
    return fromSymMatrix(ctxPtr, curl(c, fVec, vVec), mr);
}

numkit::Value symLaplacian(keel::ArrayRef<numkit::Value> args,
                           keel::Allocator *mr)
{
    symLaplacian_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    Expr f = toSymExpr(args[0], c, "laplacian");
    keel::Array<Expr> vars;
    if (args.size() >= 2) {
        vars = toSymVector(args[1], c, "laplacian");
    } else {
        SymbolNameSet symSet;
        collectSymbolsRec(c, f, symSet);
        for (const auto &nm : symSet)
            vars.push_back(c.symbol(nm));
        if (vars.empty())
            vars.push_back(c.symbol("x"));
    }
    return fromSymExpr(ctxPtr, laplacian(c, f, vars), mr);
}

numkit::Value symWronskian(keel::ArrayRef<numkit::Value> args,
                           keel::Allocator *mr)
{
    symWronskian_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    keel::Array<Expr> funcs = toSymVector(args[0], c, "wronskian");
    Expr var = (args.size() >= 2) ? toSymExpr(args[1], c, "wronskian")
                                  : defaultSymVar(c, args[0]);
    return fromSymExpr(ctxPtr, wronskian(c, funcs, var), mr);
}

numkit::Value symPotential(const numkit::Value &F, const numkit::Value &vars,
                           keel::Allocator *mr)
{
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    keel::Array<Expr> fVec = toSymVector(F, c, "potential");
    keel::Array<Expr> vVec = toSymVector(vars, c, "potential");
    PotentialResult res = scalarPotential(c, fVec, vVec);
    if (!res.proved()) {
        casFail("nk:potential:notConservative",
                keel::format("potential: vector field is not conservative ({})", res.reason));
    }
    return fromSymExpr(ctxPtr, res.phi, mr);
}

numkit::Value symEulerLagrange(keel::ArrayRef<numkit::Value> args,
                               keel::Allocator *mr)
{
    symEulerLagrange_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    Expr L = toSymExpr(args[0], c, "eulerlagrange");
    Expr t = toSymExpr(args[1], c, "eulerlagrange");
    keel::Array<Expr> q = toSymVector(args[2], c, "eulerlagrange");
    keel::Array<Expr> dq = toSymVector(args[3], c, "eulerlagrange");
    keel::Array<Expr> ddq = (args.size() >= 5) ? toSymVector(args[4], c, "eulerlagrange")
                                               : keel::Array<Expr>{};
    EulerLagrangeResult res = eulerLagrange(c, L, t, q, dq, ddq);
    return fromSymVector(ctxPtr, res.equations, /*column=*/true, mr);
}

numkit::Value symHamiltonian(keel::ArrayRef<numkit::Value> args,
                             keel::Allocator *mr)
{
    symHamiltonian_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    Expr H = toSymExpr(args[0], c, "hamiltonian");
    keel::Array<Expr> q = toSymVector(args[1], c, "hamiltonian");
    keel::Array<Expr> p = toSymVector(args[2], c, "hamiltonian");
    HamiltonEquationsResult res = hamiltonEquations(c, H, q, p);
    if (!res.certified) {
        casFail("nk:hamiltonian:failed", keel::format("hamiltonian: {}", res.reason));
    }
    Value s = Value::structure(mr);
    s.field("H") = fromSymExpr(ctxPtr, res.H, mr);
    s.field("dqdt") = fromSymVector(ctxPtr, res.dqdt, /*column=*/true, mr);
    s.field("dpdt") = fromSymVector(ctxPtr, res.dpdt, /*column=*/true, mr);
    return s;
}

numkit::Value symLegendreTransform(keel::ArrayRef<numkit::Value> args,
                                   keel::Allocator *mr)
{
    symLegendreTransform_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    Expr L = toSymExpr(args[0], c, "legendretransform");
    keel::Array<Expr> q = toSymVector(args[1], c, "legendretransform");
    keel::Array<Expr> dq = toSymVector(args[2], c, "legendretransform");
    keel::Array<Expr> p = toSymVector(args[3], c, "legendretransform");
    HamiltonEquationsResult res = legendreTransform(c, L, q, dq, p);
    if (!res.certified) {
        casFail("nk:legendretransform:failed", keel::format("legendretransform: {}", res.reason));
    }
    Value s = Value::structure(mr);
    s.field("H") = fromSymExpr(ctxPtr, res.H, mr);
    s.field("dqdt") = fromSymVector(ctxPtr, res.dqdt, /*column=*/true, mr);
    s.field("dpdt") = fromSymVector(ctxPtr, res.dpdt, /*column=*/true, mr);
    return s;
}

numkit::Value symPoissonBracket(keel::ArrayRef<numkit::Value> args,
                                keel::Allocator *mr)
{
    symPoissonBracket_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    Expr f = toSymExpr(args[0], c, "poissonbracket");
    Expr g = toSymExpr(args[1], c, "poissonbracket");
    keel::Array<Expr> q = toSymVector(args[2], c, "poissonbracket");
    keel::Array<Expr> p = toSymVector(args[3], c, "poissonbracket");
    Expr out = poissonBracket(c, f, g, q, p);
    if (out.isNull()) {
        casFail("nk:poissonbracket:failed", "poissonbracket: q and p must have the same length");
    }
    return fromSymExpr(ctxPtr, out, mr);
}

numkit::Value symLagrangeExtrema(keel::ArrayRef<numkit::Value> args,
                                 keel::Allocator *mr)
{
    symLagrangeExtrema_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    Expr f = toSymExpr(args[0], c, "lagrangeextrema");
    keel::Array<Expr> vars = toSymVector(args[1], c, "lagrangeextrema");
    keel::Array<Expr> constraints = (args.size() >= 3) ? toSymVector(args[2], c, "lagrangeextrema")
                                                       : keel::Array<Expr>{};
    LagrangeExtremaResult res = lagrangeExtrema(c, f, vars, constraints);
    if (!res.proved()) {
        casFail("nk:lagrangeextrema:failed", keel::format("lagrangeextrema: {}", res.reason));
    }
    keel::Array<Expr> vals;
    vals.reserve(res.points.size());
    for (const auto &pt : res.points)
        vals.push_back(pt.value);
    return fromSymVector(ctxPtr, vals, /*column=*/true, mr);
}

numkit::Value symFrenetSerret(keel::ArrayRef<numkit::Value> args,
                              keel::Allocator *mr)
{
    symFrenetSerret_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    keel::Array<Expr> curve = toSymVector(args[0], c, "frenetserret");
    Expr t = (args.size() >= 2) ? toSymExpr(args[1], c, "frenetserret")
                                : defaultSymVar(c, args[0], "t");
    FrenetSerretResult res = frenetSerret(c, curve, t);
    if (!res.certified) {
        casFail("nk:frenetserret:failed", keel::format("frenetserret: {}", res.reason));
    }
    Value s = Value::structure(mr);
    s.field("T") = fromSymVector(ctxPtr, res.T, /*column=*/true, mr);
    s.field("N") = fromSymVector(ctxPtr, res.N, /*column=*/true, mr);
    s.field("B") = fromSymVector(ctxPtr, res.B, /*column=*/true, mr);
    s.field("speed") = fromSymExpr(ctxPtr, res.speed, mr);
    s.field("curvature") = fromSymExpr(ctxPtr, res.curvature, mr);
    s.field("torsion") = fromSymExpr(ctxPtr, res.torsion, mr);
    return s;
}

numkit::Value symSurfaceCurvature(keel::ArrayRef<numkit::Value> args,
                                  keel::Allocator *mr)
{
    symSurfaceCurvature_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    keel::Array<Expr> surf = toSymVector(args[0], c, "surfacecurvature");
    Expr u = toSymExpr(args[1], c, "surfacecurvature");
    Expr v = toSymExpr(args[2], c, "surfacecurvature");
    SurfaceCurvatureResult res = surfaceCurvature(c, surf, u, v);
    if (!res.certified) {
        casFail("nk:surfacecurvature:failed", keel::format("surfacecurvature: {}", res.reason));
    }
    Value s = Value::structure(mr);
    s.field("firstForm") = fromSymMatrix(ctxPtr, res.firstForm, mr);
    s.field("secondForm") = fromSymMatrix(ctxPtr, res.secondForm, mr);
    s.field("shapeOperator") = fromSymMatrix(ctxPtr, res.shapeOperator, mr);
    s.field("normal") = fromSymVector(ctxPtr, res.normal, /*column=*/true, mr);
    s.field("gaussianCurvature") = fromSymExpr(ctxPtr, res.gaussianCurvature, mr);
    s.field("meanCurvature") = fromSymExpr(ctxPtr, res.meanCurvature, mr);
    return s;
}

numkit::Value symChristoffel(const numkit::Value &metric, const numkit::Value &coords,
                             keel::Allocator *mr)
{
    symMatrixSquare_argcheck("christoffel", metric);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    SymMatrix g = toSymMatrix(metric, c, "christoffel");
    keel::Array<Expr> x = toSymVector(coords, c, "christoffel");
    ChristoffelResult res = christoffelSymbols(c, g, x);
    if (!res.certified) {
        casFail("nk:christoffel:failed", keel::format("christoffel: {}", res.reason));
    }
    Value s = Value::structure(mr);
    s.field("inverseMetric") = fromSymMatrix(ctxPtr, res.inverseMetric, mr);
    Value gammaCell = Value::cell(1, res.secondKind.size(), mr);
    for (keel::usize k = 0; k < res.secondKind.size(); ++k)
        gammaCell.cellAt(k) = fromSymMatrix(ctxPtr, res.secondKind[k], mr);
    s.field("secondKind") = keel::move(gammaCell);
    return s;
}

numkit::Value symRiemann(const numkit::Value &metric, const numkit::Value &coords,
                         keel::Allocator *mr)
{
    symMatrixSquare_argcheck("riemann", metric);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    SymMatrix g = toSymMatrix(metric, c, "riemann");
    keel::Array<Expr> x = toSymVector(coords, c, "riemann");
    RiemannCurvatureResult res = riemannTensor(c, g, x);
    if (!res.certified) {
        casFail("nk:riemann:failed", keel::format("riemann: {}", res.reason));
    }
    Value s = Value::structure(mr);
    s.field("ricci") = fromSymMatrix(ctxPtr, res.ricci, mr);
    s.field("scalarCurvature") = fromSymExpr(ctxPtr, res.scalarCurvature, mr);
    s.field("einstein") = fromSymMatrix(ctxPtr, res.einstein, mr);
    return s;
}

numkit::Value symRicci(const numkit::Value &metric, const numkit::Value &coords,
                       keel::Allocator *mr)
{
    symMatrixSquare_argcheck("ricci", metric);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    SymMatrix g = toSymMatrix(metric, c, "ricci");
    keel::Array<Expr> x = toSymVector(coords, c, "ricci");
    SymMatrix R = ricciTensor(c, g, x);
    if (R.empty() && !g.empty()) {
        casFail("nk:ricci:failed", "ricci: metric is singular or dimensions do not match coordinates");
    }
    return fromSymMatrix(ctxPtr, R, mr);
}

numkit::Value symScalarCurvature(const numkit::Value &metric, const numkit::Value &coords,
                                 keel::Allocator *mr)
{
    symMatrixSquare_argcheck("scalarcurvature", metric);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    SymMatrix g = toSymMatrix(metric, c, "scalarcurvature");
    keel::Array<Expr> x = toSymVector(coords, c, "scalarcurvature");
    Expr R = scalarCurvature(c, g, x);
    if (R.isNull()) {
        casFail("nk:scalarcurvature:failed", "scalarcurvature: metric is singular or dimensions do not match");
    }
    return fromSymExpr(ctxPtr, R, mr);
}

numkit::Value symGeodesic(keel::ArrayRef<numkit::Value> args,
                          keel::Allocator *mr)
{
    symGeodesic_argcheck(args);
    symMatrixSquare_argcheck("geodesic", args[0]);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    SymMatrix g = toSymMatrix(args[0], c, "geodesic");
    keel::Array<Expr> x = toSymVector(args[1], c, "geodesic");
    keel::Array<Expr> vel = (args.size() >= 3) ? toSymVector(args[2], c, "geodesic") : keel::Array<Expr>{};
    keel::Array<Expr> acc = (args.size() >= 4) ? toSymVector(args[3], c, "geodesic") : keel::Array<Expr>{};
    GeodesicResult res = geodesicEquations(c, g, x, vel, acc);
    if (!res.certified) {
        casFail("nk:geodesic:failed", keel::format("geodesic: {}", res.reason));
    }
    return fromSymVector(ctxPtr, res.equations, /*column=*/true, mr);
}

numkit::Value symLineIntegral(keel::ArrayRef<numkit::Value> args,
                              keel::Allocator *mr)
{
    symLineIntegral_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    keel::Array<Expr> vars = toSymVector(args[1], c, "lineintegral");
    keel::Array<Expr> curve = toSymVector(args[2], c, "lineintegral");
    Expr t = toSymExpr(args[3], c, "lineintegral");
    Expr a = toSymExpr(args[4], c, "lineintegral");
    Expr b = toSymExpr(args[5], c, "lineintegral");
    DefiniteIntegral res;
    if (args[0].numel() > 1) {
        keel::Array<Expr> field = toSymVector(args[0], c, "lineintegral");
        res = lineIntegralVector(c, field, vars, curve, t, a, b);
    } else {
        Expr f = toSymExpr(args[0], c, "lineintegral");
        res = lineIntegralScalar(c, f, vars, curve, t, a, b);
    }
    if (!res.proved()) {
        casFail("nk:lineintegral:failed", keel::format("lineintegral: {}", res.reason));
    }
    return fromSymExpr(ctxPtr, res.value, mr);
}

numkit::Value symSurfaceIntegral(keel::ArrayRef<numkit::Value> args,
                                 keel::Allocator *mr)
{
    symSurfaceIntegral_argcheck(args);
    mr = resolveMr(mr);
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    keel::Array<Expr> vars = toSymVector(args[1], c, "surfaceintegral");
    keel::Array<Expr> surface = toSymVector(args[2], c, "surfaceintegral");
    DefiniteBound uBound{toSymExpr(args[3], c, "surfaceintegral"),
                         toSymExpr(args[4], c, "surfaceintegral"),
                         toSymExpr(args[5], c, "surfaceintegral")};
    DefiniteBound vBound{toSymExpr(args[6], c, "surfaceintegral"),
                         toSymExpr(args[7], c, "surfaceintegral"),
                         toSymExpr(args[8], c, "surfaceintegral")};
    DefiniteIntegral res;
    if (args[0].numel() > 1) {
        keel::Array<Expr> field = toSymVector(args[0], c, "surfaceintegral");
        res = surfaceIntegralVector(c, field, vars, surface, uBound, vBound);
    } else {
        Expr f = toSymExpr(args[0], c, "surfaceintegral");
        res = surfaceIntegralScalar(c, f, vars, surface, uBound, vBound);
    }
    if (!res.proved()) {
        casFail("nk:surfaceintegral:failed", keel::format("surfaceintegral: {}", res.reason));
    }
    return fromSymExpr(ctxPtr, res.value, mr);
}

numkit::Value symElemFunc1(keel::StringRef fnName, const numkit::Value &v,
                           keel::Allocator *mr)
{
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    keel::String fnStr = keel::String::from(fnName);
    return mapSymUnary(v, c, [&](Expr e) {
        if (fnStr.as_ref() == "sqrt") {
            return c.pow(e, c.number(Rational(1, 2)));
        }
        return c.func(fnStr, e);
    }, mr, fnStr.c_str());
}

numkit::Value symElemFunc2(keel::StringRef fnName, const numkit::Value &a,
                           const numkit::Value &b,
                           keel::Allocator *mr)
{
    auto ctxPtr = defaultCtx();
    Ctx &c = *ctxPtr;
    keel::String fnStr = keel::String::from(fnName);
    return mapSymElementwiseBinary(a, b, c, [&](Expr x, Expr y) {
        return c.func(fnStr, x, y);
    }, mr, fnStr.c_str());
}

// ============================================================================
// BuiltinClass("sym") construction
// ============================================================================

numkit::BuiltinClass makeSymBuiltinClass()
{
    BuiltinClass cls;
    cls.name = keel::String::from("sym");
    cls.isHandle = false;

    cls.construct = [](keel::ArrayRef<Value> args, CallContext &ctx) -> Value {
        keel::Allocator *mr = ctx.engine ? ctx.engine->allocator() : nullptr;
        return symCreate(args, mr);
    };

    cls.dispText = [](const Value &self) -> keel::String {
        auto ctxPtr = defaultCtx();
        Ctx &c = *ctxPtr;
        if (self.objectCount() == 0)
            return keel::String::from("  [empty sym]\n");
        if (self.objectCount() == 1 && self.dims().rows() == 1 && self.dims().cols() == 1)
            return keel::format("  {}\n", c.toString(toSymExpr(self, c, "disp")));
        return keel::format("  {}\n", toSymMatrix(self, c, "disp").toString(c));
    };

    // Binary & unary operator overloads
    cls.ops.put(keel::String::from("plus"), [](Value &, keel::ArrayRef<Value> args, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        keel::Allocator *mr = ctx.engine ? ctx.engine->allocator() : nullptr;
        auto ctxPtr = defaultCtx();
        Ctx &c = *ctxPtr;
        outs[0] = mapSymElementwiseBinary(args[0], args[1], c, [&](Expr a, Expr b) {
            return c.add({a, b});
        }, mr, "plus");
    });

    cls.ops.put(keel::String::from("minus"), [](Value &, keel::ArrayRef<Value> args, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        keel::Allocator *mr = ctx.engine ? ctx.engine->allocator() : nullptr;
        auto ctxPtr = defaultCtx();
        Ctx &c = *ctxPtr;
        outs[0] = mapSymElementwiseBinary(args[0], args[1], c, [&](Expr a, Expr b) {
            return c.add({a, c.neg(b)});
        }, mr, "minus");
    });

    cls.ops.put(keel::String::from("uminus"), [](Value &self, keel::ArrayRef<Value>, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        keel::Allocator *mr = ctx.engine ? ctx.engine->allocator() : nullptr;
        auto ctxPtr = defaultCtx();
        Ctx &c = *ctxPtr;
        outs[0] = mapSymUnary(self, c, [&](Expr a) { return c.neg(a); }, mr, "uminus");
    });

    cls.ops.put(keel::String::from("uplus"), [](Value &self, keel::ArrayRef<Value>, keel::usize, keel::MutArrayRef<Value> outs, CallContext &) {
        outs[0] = self;
    });

    cls.ops.put(keel::String::from("times"), [](Value &, keel::ArrayRef<Value> args, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        keel::Allocator *mr = ctx.engine ? ctx.engine->allocator() : nullptr;
        auto ctxPtr = defaultCtx();
        Ctx &c = *ctxPtr;
        outs[0] = mapSymElementwiseBinary(args[0], args[1], c, [&](Expr a, Expr b) {
            return c.mul({a, b});
        }, mr, "times");
    });

    cls.ops.put(keel::String::from("mtimes"), [](Value &, keel::ArrayRef<Value> args, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        keel::Allocator *mr = ctx.engine ? ctx.engine->allocator() : nullptr;
        auto ctxPtr = defaultCtx();
        Ctx &c = *ctxPtr;
        SymMatrix A = toSymMatrix(args[0], c, "mtimes");
        SymMatrix B = toSymMatrix(args[1], c, "mtimes");
        if (A.rows() == 1 && A.cols() == 1) {
            outs[0] = fromSymMatrix(ctxPtr, B.scale(c, A(0, 0)), mr);
            return;
        }
        if (B.rows() == 1 && B.cols() == 1) {
            outs[0] = fromSymMatrix(ctxPtr, A.scale(c, B(0, 0)), mr);
            return;
        }
        if (A.cols() != B.rows()) {
            casFail("nk:mtimes:innerDimMismatch",
                        "mtimes: inner matrix dimensions must agree");
        }
        outs[0] = fromSymMatrix(ctxPtr, A.mul(c, B), mr);
    });

    cls.ops.put(keel::String::from("rdivide"), [](Value &, keel::ArrayRef<Value> args, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        keel::Allocator *mr = ctx.engine ? ctx.engine->allocator() : nullptr;
        auto ctxPtr = defaultCtx();
        Ctx &c = *ctxPtr;
        outs[0] = mapSymElementwiseBinary(args[0], args[1], c, [&](Expr a, Expr b) {
            if (c.isZero(b))
                casFail("nk:rdivide:divByZero", "rdivide: symbolic division by zero");
            return c.div(a, b);
        }, mr, "rdivide");
    });

    cls.ops.put(keel::String::from("mrdivide"), [](Value &, keel::ArrayRef<Value> args, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        keel::Allocator *mr = ctx.engine ? ctx.engine->allocator() : nullptr;
        auto ctxPtr = defaultCtx();
        Ctx &c = *ctxPtr;
        SymMatrix B = toSymMatrix(args[1], c, "mrdivide");
        if (B.rows() == 1 && B.cols() == 1) {
            if (c.isZero(B(0, 0)))
                casFail("nk:mrdivide:divByZero", "mrdivide: symbolic division by zero");
            outs[0] = mapSymElementwiseBinary(args[0], args[1], c, [&](Expr a, Expr b) {
                return c.div(a, b);
            }, mr, "mrdivide");
            return;
        }
        SymMatrix A = toSymMatrix(args[0], c, "mrdivide");
        if (!B.isSquare() || A.cols() != B.rows()) {
            casFail("nk:mrdivide:dimMismatch", "mrdivide: matrix dimensions must agree");
        }
        SymMatrix Binv = inv(c, B);
        if (Binv.empty())
            casFail("nk:mrdivide:singular", "mrdivide: divisor matrix is singular");
        outs[0] = fromSymMatrix(ctxPtr, A.mul(c, Binv), mr);
    });

    cls.ops.put(keel::String::from("ldivide"), [](Value &, keel::ArrayRef<Value> args, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        keel::Allocator *mr = ctx.engine ? ctx.engine->allocator() : nullptr;
        auto ctxPtr = defaultCtx();
        Ctx &c = *ctxPtr;
        outs[0] = mapSymElementwiseBinary(args[0], args[1], c, [&](Expr a, Expr b) {
            if (c.isZero(a))
                casFail("nk:ldivide:divByZero", "ldivide: symbolic division by zero");
            return c.div(b, a);
        }, mr, "ldivide");
    });

    cls.ops.put(keel::String::from("mldivide"), [](Value &, keel::ArrayRef<Value> args, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        keel::Allocator *mr = ctx.engine ? ctx.engine->allocator() : nullptr;
        auto ctxPtr = defaultCtx();
        Ctx &c = *ctxPtr;
        SymMatrix A = toSymMatrix(args[0], c, "mldivide");
        if (A.rows() == 1 && A.cols() == 1) {
            if (c.isZero(A(0, 0)))
                casFail("nk:mldivide:divByZero", "mldivide: symbolic division by zero");
            outs[0] = mapSymElementwiseBinary(args[0], args[1], c, [&](Expr a, Expr b) {
                return c.div(b, a);
            }, mr, "mldivide");
            return;
        }
        outs[0] = symLinsolve(args[0], args[1], mr);
    });

    cls.ops.put(keel::String::from("power"), [](Value &, keel::ArrayRef<Value> args, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        keel::Allocator *mr = ctx.engine ? ctx.engine->allocator() : nullptr;
        auto ctxPtr = defaultCtx();
        Ctx &c = *ctxPtr;
        outs[0] = mapSymElementwiseBinary(args[0], args[1], c, [&](Expr a, Expr b) {
            return c.pow(a, b);
        }, mr, "power");
    });

    cls.ops.put(keel::String::from("mpower"), [](Value &, keel::ArrayRef<Value> args, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        keel::Allocator *mr = ctx.engine ? ctx.engine->allocator() : nullptr;
        auto ctxPtr = defaultCtx();
        Ctx &c = *ctxPtr;
        SymMatrix A = toSymMatrix(args[0], c, "mpower");
        SymMatrix B = toSymMatrix(args[1], c, "mpower");
        if (A.rows() == 1 && A.cols() == 1 && B.rows() == 1 && B.cols() == 1) {
            outs[0] = fromSymExpr(ctxPtr, c.pow(A(0, 0), B(0, 0)), mr);
            return;
        }
        if (!A.isSquare() || B.rows() != 1 || B.cols() != 1 || c.kind(B(0, 0)) != NodeKind::Number) {
            casFail("nk:mpower:invalidMatrixPower",
                        "mpower: matrix power requires a square matrix and an integer scalar exponent");
        }
        const Rational &rn = c.numberValue(B(0, 0));
        keel::i64 expI64 = 0;
        if (!rn.fitsInt64(expI64)) {
            casFail("nk:mpower:nonIntegerMatrixPower",
                        "mpower: matrix exponent must be an integer");
        }
        keel::i32 n = keel::as<keel::i32>(expI64);
        SymMatrix base = A;
        if (n < 0) {
            base = inv(c, A);
            if (base.empty())
                casFail("nk:mpower:singular", "mpower: matrix is singular");
            n = -n;
        }
        SymMatrix res = SymMatrix::eye(c, A.rows());
        while (n > 0) {
            if (n & 1)
                res = res.mul(c, base);
            base = base.mul(c, base);
            n >>= 1;
        }
        outs[0] = fromSymMatrix(ctxPtr, res, mr);
    });

    auto transposeOp = [](Value &self, keel::ArrayRef<Value>, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        keel::Allocator *mr = ctx.engine ? ctx.engine->allocator() : nullptr;
        outs[0] = self.objectTranspose(mr);
    };
    cls.ops.put(keel::String::from("transpose"), transposeOp);
    cls.ops.put(keel::String::from("ctranspose"), transposeOp);

    auto makeRelOp = [](const char *casRelName, const char *opLabel) {
        return [casRelName, opLabel](Value &, keel::ArrayRef<Value> args, keel::usize,
                                     keel::MutArrayRef<Value> outs, CallContext &ctx) {
            keel::Allocator *mr = ctx.engine ? ctx.engine->allocator() : nullptr;
            auto ctxPtr = defaultCtx();
            Ctx &c = *ctxPtr;
            outs[0] = mapSymElementwiseBinary(args[0], args[1], c, [&](Expr a, Expr b) {
                return c.func(casRelName, a, b);
            }, mr, opLabel);
        };
    };

    cls.ops.put(keel::String::from("eq"), makeRelOp("__eq", "eq"));
    cls.ops.put(keel::String::from("ne"), makeRelOp("__ne", "ne"));
    cls.ops.put(keel::String::from("lt"), makeRelOp("__lt", "lt"));
    cls.ops.put(keel::String::from("le"), makeRelOp("__le", "le"));
    cls.ops.put(keel::String::from("gt"), makeRelOp("__gt", "gt"));
    cls.ops.put(keel::String::from("ge"), makeRelOp("__ge", "ge"));

    // Elementary & special 1-argument functions on sym
    const char *kUnaryElemFns[] = {
        "sin", "cos", "tan", "asin", "acos", "atan",
        "sinh", "cosh", "tanh", "asinh", "acosh", "atanh",
        "exp", "log", "sqrt", "abs", "erf", "erfc", "erfi",
        "gamma", "airyAi", "airyBi", "heaviside", "dirac", "zeta", "Ei"
    };
    for (const char *fn : kUnaryElemFns) {
        cls.methods.put(keel::String::from(fn), [fn](Value &self, keel::ArrayRef<Value> rest, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
            if (!rest.empty()) {
                casFail(keel::format("nk:{}:tooManyInputs", fn),
                        keel::format("{}: expected 1 input argument", fn));
            }
            keel::Allocator *mr = ctx.engine ? ctx.engine->allocator() : nullptr;
            outs[0] = symElemFunc1(fn, self, mr);
        });
    }

    // Two-argument special functions when first arg is sym
    struct BinarySpecMap {
        const char *mName;
        const char *casName;
    };
    const BinarySpecMap kBinarySpecFns[] = {
        {"besselj", "besselJ"}, {"bessely", "besselY"},
        {"besseli", "besselI"}, {"besselk", "besselK"},
        {"besselJ", "besselJ"}, {"besselY", "besselY"},
        {"besselI", "besselI"}, {"besselK", "besselK"},
        {"legendreP", "legendreP"}, {"legendreQ", "legendreQ"},
        {"chebyshevT", "chebyshevT"}, {"chebyshevU", "chebyshevU"},
        {"hermiteH", "hermiteH"}, {"laguerreL", "laguerreL"}
    };
    for (const auto &entry : kBinarySpecFns) {
        const char *mName = entry.mName;
        const char *casName = entry.casName;
        cls.methods.put(keel::String::from(mName), [mName, casName](Value &self, keel::ArrayRef<Value> rest, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
            if (rest.size() != 1) {
                casFail(keel::format("nk:{}:arity", mName),
                        keel::format("{}: expected 2 input arguments", mName));
            }
            keel::Allocator *mr = ctx.engine ? ctx.engine->allocator() : nullptr;
            outs[0] = symElemFunc2(casName, self, rest[0], mr);
        });
    }

    auto prependSelf = [](const Value &self, keel::ArrayRef<Value> rest) {
        keel::Array<Value> all;
        all.reserve(1 + rest.size());
        all.push_back(self);
        for (keel::usize i = 0; i < rest.size(); ++i)
            all.push_back(rest[i]);
        return all;
    };

    cls.methods.put(keel::String::from("double"), [](Value &self, keel::ArrayRef<Value>, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        outs[0] = symDouble(self, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("vpa"), [prependSelf](Value &self, keel::ArrayRef<Value> rest, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        auto all = prependSelf(self, rest);
        outs[0] = symVpa(all, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("char"), [](Value &self, keel::ArrayRef<Value>, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        outs[0] = symChar(self, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("latex"), [](Value &self, keel::ArrayRef<Value>, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        outs[0] = symLatex(self, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("ccode"), [](Value &self, keel::ArrayRef<Value>, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        outs[0] = symCCode(self, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("pretty"), [](Value &self, keel::ArrayRef<Value>, keel::usize nargout, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        Value s = symPretty(self, ctx.engine ? ctx.engine->allocator() : nullptr);
        if (nargout == 0 && ctx.engine) {
            if (const ExternalFunc *dispFn = ctx.engine->findExternal("disp", ctx.env)) {
                Value dargs[1] = {s};
                Value douts[1];
                (*dispFn)(keel::ArrayRef<Value>(dargs, 1), 0, keel::MutArrayRef<Value>(douts, 1), ctx);
            }
        } else {
            outs[0] = keel::move(s);
        }
    });
    cls.methods.put(keel::String::from("simplify"), [](Value &self, keel::ArrayRef<Value>, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        outs[0] = symSimplify(self, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("expand"), [](Value &self, keel::ArrayRef<Value>, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        outs[0] = symExpand(self, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("factor"), [prependSelf](Value &self, keel::ArrayRef<Value> rest, keel::usize nargout, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        auto all = prependSelf(self, rest);
        symFactor(all, nargout, outs, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("collect"), [prependSelf](Value &self, keel::ArrayRef<Value> rest, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        auto all = prependSelf(self, rest);
        outs[0] = symCollect(all, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("coeffs"), [prependSelf](Value &self, keel::ArrayRef<Value> rest, keel::usize nargout, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        auto all = prependSelf(self, rest);
        symCoeffs(all, nargout, outs, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("numden"), [](Value &self, keel::ArrayRef<Value>, keel::usize nargout, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        symNumden(self, nargout, outs, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("partfrac"), [prependSelf](Value &self, keel::ArrayRef<Value> rest, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        auto all = prependSelf(self, rest);
        outs[0] = symPartfrac(all, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("subs"), [prependSelf](Value &self, keel::ArrayRef<Value> rest, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        auto all = prependSelf(self, rest);
        outs[0] = symSubs(all, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("symvar"), [prependSelf](Value &self, keel::ArrayRef<Value> rest, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        auto all = prependSelf(self, rest);
        outs[0] = symSymvar(all, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("sym2poly"), [prependSelf](Value &self, keel::ArrayRef<Value> rest, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        auto all = prependSelf(self, rest);
        outs[0] = symSym2poly(all, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("diff"), [prependSelf](Value &self, keel::ArrayRef<Value> rest, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        auto all = prependSelf(self, rest);
        outs[0] = symDiff(all, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("int"), [prependSelf](Value &self, keel::ArrayRef<Value> rest, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        auto all = prependSelf(self, rest);
        outs[0] = symInt(all, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("limit"), [prependSelf](Value &self, keel::ArrayRef<Value> rest, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        auto all = prependSelf(self, rest);
        outs[0] = symLimit(all, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("taylor"), [prependSelf](Value &self, keel::ArrayRef<Value> rest, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        auto all = prependSelf(self, rest);
        outs[0] = symTaylor(all, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("laurent"), [prependSelf](Value &self, keel::ArrayRef<Value> rest, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        auto all = prependSelf(self, rest);
        outs[0] = symLaurent(all, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("mtaylor"), [prependSelf](Value &self, keel::ArrayRef<Value> rest, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        auto all = prependSelf(self, rest);
        outs[0] = symMtaylor(all, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("pade"), [prependSelf](Value &self, keel::ArrayRef<Value> rest, keel::usize nargout, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        auto all = prependSelf(self, rest);
        symPade(all, nargout, outs, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("residue"), [prependSelf](Value &self, keel::ArrayRef<Value> rest, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        auto all = prependSelf(self, rest);
        outs[0] = symResidue(all, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("symsum"), [prependSelf](Value &self, keel::ArrayRef<Value> rest, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        auto all = prependSelf(self, rest);
        outs[0] = symSymsum(all, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("solve"), [prependSelf](Value &self, keel::ArrayRef<Value> rest, keel::usize nargout, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        auto all = prependSelf(self, rest);
        symSolve(all, nargout, outs, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("dsolve"), [prependSelf](Value &self, keel::ArrayRef<Value> rest, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        auto all = prependSelf(self, rest);
        outs[0] = symDsolve(all, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("laplace"), [prependSelf](Value &self, keel::ArrayRef<Value> rest, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        auto all = prependSelf(self, rest);
        outs[0] = symLaplace(all, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("ilaplace"), [prependSelf](Value &self, keel::ArrayRef<Value> rest, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        auto all = prependSelf(self, rest);
        outs[0] = symIlaplace(all, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("fourier"), [prependSelf](Value &self, keel::ArrayRef<Value> rest, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        auto all = prependSelf(self, rest);
        outs[0] = symFourier(all, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("ifourier"), [prependSelf](Value &self, keel::ArrayRef<Value> rest, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        auto all = prependSelf(self, rest);
        outs[0] = symIfourier(all, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("ztrans"), [prependSelf](Value &self, keel::ArrayRef<Value> rest, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        auto all = prependSelf(self, rest);
        outs[0] = symZtrans(all, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("iztrans"), [prependSelf](Value &self, keel::ArrayRef<Value> rest, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        auto all = prependSelf(self, rest);
        outs[0] = symIztrans(all, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("det"), [](Value &self, keel::ArrayRef<Value>, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        outs[0] = symDet(self, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("inv"), [](Value &self, keel::ArrayRef<Value>, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        outs[0] = symInv(self, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("trace"), [](Value &self, keel::ArrayRef<Value>, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        outs[0] = symTrace(self, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    auto adjugateMethod = [](Value &self, keel::ArrayRef<Value>, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        outs[0] = symAdjugate(self, ctx.engine ? ctx.engine->allocator() : nullptr);
    };
    cls.methods.put(keel::String::from("adjugate"), adjugateMethod);
    cls.methods.put(keel::String::from("adjoint"), adjugateMethod);
    cls.methods.put(keel::String::from("charpoly"), [prependSelf](Value &self, keel::ArrayRef<Value> rest, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        auto all = prependSelf(self, rest);
        outs[0] = symCharpoly(all, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("rank"), [](Value &self, keel::ArrayRef<Value>, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        outs[0] = symRank(self, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("rref"), [](Value &self, keel::ArrayRef<Value>, keel::usize nargout, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        symRref(self, nargout, outs, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    auto nullMethod = [](Value &self, keel::ArrayRef<Value>, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        outs[0] = symNull(self, ctx.engine ? ctx.engine->allocator() : nullptr);
    };
    cls.methods.put(keel::String::from("null"), nullMethod);
    cls.methods.put(keel::String::from("nullspace"), nullMethod);
    cls.methods.put(keel::String::from("linsolve"), [](Value &self, keel::ArrayRef<Value> rest, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        argcheck::checkNargin(rest.size() + 1, 2, 2, "linsolve");
        outs[0] = symLinsolve(self, rest[0], ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("lu"), [](Value &self, keel::ArrayRef<Value>, keel::usize nargout, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        symLu(self, nargout, outs, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("qr"), [](Value &self, keel::ArrayRef<Value>, keel::usize nargout, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        symQr(self, nargout, outs, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("eig"), [](Value &self, keel::ArrayRef<Value>, keel::usize nargout, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        symEig(self, nargout, outs, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("jordan"), [](Value &self, keel::ArrayRef<Value>, keel::usize nargout, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        symJordan(self, nargout, outs, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("expm"), [prependSelf](Value &self, keel::ArrayRef<Value> rest, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        auto all = prependSelf(self, rest);
        outs[0] = symExpm(all, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("jacobian"), [prependSelf](Value &self, keel::ArrayRef<Value> rest, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        auto all = prependSelf(self, rest);
        outs[0] = symJacobian(all, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("gradient"), [prependSelf](Value &self, keel::ArrayRef<Value> rest, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        auto all = prependSelf(self, rest);
        outs[0] = symGradient(all, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("hessian"), [prependSelf](Value &self, keel::ArrayRef<Value> rest, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        auto all = prependSelf(self, rest);
        outs[0] = symHessian(all, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("divergence"), [](Value &self, keel::ArrayRef<Value> rest, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        argcheck::checkNargin(rest.size() + 1, 2, 2, "divergence");
        outs[0] = symDivergence(self, rest[0], ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("curl"), [](Value &self, keel::ArrayRef<Value> rest, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        argcheck::checkNargin(rest.size() + 1, 2, 2, "curl");
        outs[0] = symCurl(self, rest[0], ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("laplacian"), [prependSelf](Value &self, keel::ArrayRef<Value> rest, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        auto all = prependSelf(self, rest);
        outs[0] = symLaplacian(all, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("wronskian"), [prependSelf](Value &self, keel::ArrayRef<Value> rest, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        auto all = prependSelf(self, rest);
        outs[0] = symWronskian(all, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("potential"), [](Value &self, keel::ArrayRef<Value> rest, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        argcheck::checkNargin(rest.size() + 1, 2, 2, "potential");
        outs[0] = symPotential(self, rest[0], ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("assume"), [](Value &self, keel::ArrayRef<Value> rest, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        argcheck::checkNargin(rest.size() + 1, 1, 2, "assume");
        keel::Allocator *mr = ctx.engine ? ctx.engine->allocator() : nullptr;
        if (rest.empty()) {
            outs[0] = symAssumeCond(self, mr);
            return;
        }
        outs[0] = symAssume(self, rest[0].toString(), mr);
    });
    cls.methods.put(keel::String::from("eval"), [](Value &self, keel::ArrayRef<Value>, keel::usize nargout, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        keel::Allocator *mr = ctx.engine ? ctx.engine->allocator() : nullptr;
        keel::String src = symEvalSource(self);
        if (ctx.engine) {
            if (const ExternalFunc *evalFn = ctx.engine->findExternal("eval", ctx.env)) {
                Value eargs[1] = {Value::fromString(src.as_ref(), mr)};
                (*evalFn)(keel::ArrayRef<Value>(eargs, 1), nargout == 0 ? 1 : nargout, outs, ctx);
                return;
            }
        }
        outs[0] = symDouble(self, mr);
    });
    cls.methods.put(keel::String::from("assumptions"), [](Value &self, keel::ArrayRef<Value>, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        outs[0] = symAssumptions(self, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("lhs"), [](Value &self, keel::ArrayRef<Value>, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        outs[0] = symLhs(self, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("rhs"), [](Value &self, keel::ArrayRef<Value>, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        outs[0] = symRhs(self, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("isAlways"), [](Value &self, keel::ArrayRef<Value>, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        outs[0] = symIsAlways(self, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("logical"), [](Value &self, keel::ArrayRef<Value>, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        outs[0] = symIsAlways(self, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("formula"), [](Value &self, keel::ArrayRef<Value>, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        outs[0] = symFormula(self, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("argnames"), [](Value &self, keel::ArrayRef<Value>, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        outs[0] = symArgnames(self, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("__indexAssign"), [](Value &, keel::ArrayRef<Value> args, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        outs[0] = symfunCreate(args, ctx.engine ? ctx.engine->allocator() : nullptr);
    });
    cls.methods.put(keel::String::from("matlabFunction"), [prependSelf](Value &self, keel::ArrayRef<Value> rest, keel::usize, keel::MutArrayRef<Value> outs, CallContext &ctx) {
        auto all = prependSelf(self, rest);
        keel::Allocator *mr = ctx.engine ? ctx.engine->allocator() : nullptr;
        keel::String src = symMatlabFunctionSource(all, mr);
        if (ctx.engine) {
            if (const ExternalFunc *s2f = ctx.engine->findExternal("str2func", ctx.env)) {
                Value sargs[1] = {Value::fromString(src, mr)};
                (*s2f)(keel::ArrayRef<Value>(sargs, 1), 1, outs, ctx);
                return;
            }
        }
        outs[0] = Value::fromString(src, mr);
    });

    return cls;
}

numkit::BuiltinClass makeSymfunBuiltinClass()
{
    BuiltinClass cls = makeSymBuiltinClass();
    cls.name = keel::String::from("symfun");
    cls.superclasses.push_back(keel::String::from("sym"));
    cls.construct = [](keel::ArrayRef<Value> args, CallContext &ctx) -> Value {
        keel::Allocator *mr = ctx.engine ? ctx.engine->allocator() : nullptr;
        return symfunCreate(args, mr);
    };
    cls.subsref = [](Value &self, keel::ArrayRef<Value> idxArgs, keel::usize,
                     keel::MutArrayRef<Value> outs, CallContext &ctx) {
        keel::Allocator *mr = resolveMr(ctx.engine ? ctx.engine->allocator() : nullptr);
        auto ctxPtr = defaultCtx();
        Ctx &c = *ctxPtr;
        const ObjectState *st = self.objectStateConst();
        if (!st || !st->native) {
            outs[0] = fromSymExpr(ctxPtr, c.zero(), mr);
            return;
        }
        const auto *sp = static_cast<const SymPayload *>(st->native.get());
        if (idxArgs.size() != sp->funParams.size()) {
            casFail("nk:symfun:arity",
                    keel::format("symfun: expected {} input argument(s), got {}",
                                 sp->funParams.size(), idxArgs.size()));
        }
        Expr res = sp->expr;
        for (keel::usize i = 0; i < idxArgs.size(); ++i) {
            Expr val = toSymExpr(idxArgs[i], c, "symfun");
            res = c.subs(res, sp->funParams[i], val);
        }
        outs[0] = fromSymExpr(ctxPtr, c.simplify(res), mr);
    };
    return cls;
}

} // namespace numkit::cas
