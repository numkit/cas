#include <keel/algo.h>
#include <keel/core.h>
#include <keel/format.h>
#include <keel/math.h>
#include <numkit/cas/core/expr.hpp>
#include <numkit/cas/poly/sturm.hpp>


namespace numkit::cas {

namespace {

constexpr keel::u32 kFnvOffset = 2166136261u;
constexpr keel::u32 kFnvPrime = 16777619u;

constexpr keel::i64 kMaxFoldExp = 65536; // numeric Pow folding bound

keel::u32 mix32(keel::u32 h, keel::u32 v)
{
    return (h ^ v) * kFnvPrime;
}

keel::u32 hashName(keel::StringRef s)
{
    keel::u32 h = kFnvOffset;
    for (char c : s)
        h = mix32(h, keel::as<keel::u8>(c));
    return h;
}

keel::i32 signOf(keel::i32 c)
{
    return c < 0 ? -1 : (c > 0 ? 1 : 0);
}

// Exponent of the printing precedence ladder; larger binds tighter.
keel::i32 precOf(NodeKind k, const Rational &num)
{
    switch (k) {
    case NodeKind::Number:
        // Non-integer rationals read ambiguously as a Pow base ("1/2^3"),
        // so they get a precedence below Pow but above Mul/Add.
        return !(num.den() == BigInt(1)) ? 55 : 100;
    case NodeKind::Symbol:
    case NodeKind::RootOf:
        return 100;
    case NodeKind::Func:
        return 90;
    case NodeKind::Pow:
        return 60;
    case NodeKind::Mul:
        return 50;
    case NodeKind::Add:
        return 40;
    }
    return 0;
}

} // namespace

Expr Ctx::number(keel::i64 v)
{
    return number(Rational(v));
}

Expr Ctx::number(Rational v)
{
    return makeNode(NodeKind::Number, 0, {}, v);
}

keel::u32 Ctx::internName(keel::StringRef name,
                              keel::HashMap<keel::String, keel::u32> &ids,
                              StableBlocks<keel::String> &names)
{
    if (const keel::u32 *hit = ids.get(name))
        return *hit;
    const keel::u32 id = keel::as<keel::u32>(names.size());
    names.push_back(keel::String::from(name));
    ids.try_insert(keel::String::from(name), id);
    return id;
}

Expr Ctx::symbol(keel::StringRef name)
{
    const keel::u32 id = internName(name, symbolIds_, symbolNames_);
    return makeNode(NodeKind::Symbol, id, {}, Rational(keel::i64{0}));
}

Expr Ctx::func(keel::StringRef name, Expr arg)
{
    const keel::u32 id = internName(name, funcIds_, funcNames_);
    return makeNode(NodeKind::Func, id, {arg}, Rational(keel::i64{0}));
}

Expr Ctx::func(keel::StringRef name, Expr arg0, Expr arg1)
{
    const keel::u32 id = internName(name, funcIds_, funcNames_);
    return makeNode(NodeKind::Func, id, {arg0, arg1}, Rational(keel::i64{0}));
}

Expr Ctx::func(keel::StringRef name, keel::ArrayRef<Expr> args)
{
    const keel::u32 id = internName(name, funcIds_, funcNames_);
    return makeNode(NodeKind::Func, id, args, Rational(keel::i64{0}));
}

Expr Ctx::rootOf(keel::Array<Rational> poly, keel::i32 index)
{
    while (poly.size() > 1 && poly.back().isZero())
        poly.pop_back();
    assert(poly.size() >= 3 && "RootOf needs degree >= 2");
    const Rational lc = poly.back();
    assert(!(lc == Rational(keel::i64{0})) && "RootOf of zero polynomial");
    assert(index >= 0);
    if (!(lc == Rational(keel::i64{1})))
        for (Rational &c : poly)
            c = c / lc;
    assert(index < keel::as<keel::i32>(poly.size()) - 1);

    keel::u32 hash = mix32(kFnvOffset, keel::as<keel::u32>(NodeKind::RootOf));
    hash = mix32(hash, keel::as<keel::u32>(index));
    for (const Rational &c : poly) {
        const keel::u64 h64 = c.hashBits();
        hash = mix32(hash, keel::as<keel::u32>(h64));
        hash = mix32(hash, keel::as<keel::u32>(h64 >> 32));
    }
    for (keel::usize i = 0; i < rootofs_.size(); ++i) {
        const RootOfDesc &d = rootofs_[i];
        if (d.index == index && d.poly == poly && d.nodeId != 0)
            return Expr(this, d.nodeId);
    }
    rootofs_.push_back(RootOfDesc{keel::move(poly), index, 0});
    const auto tableIdx = keel::as<keel::u32>(rootofs_.size() - 1);
    const Expr made = makeNode(NodeKind::RootOf, tableIdx, {}, Rational(keel::i64{0}));
    rootofs_[tableIdx].nodeId = id(made);
    return made;
}

const keel::Array<Rational> &Ctx::rootOfPoly(Expr e) const
{
    assert(kind(e) == NodeKind::RootOf);
    return rootofs_[node(e).aux].poly;
}

keel::i32 Ctx::rootOfIndex(Expr e) const
{
    assert(kind(e) == NodeKind::RootOf);
    return rootofs_[node(e).aux].index;
}

Expr Ctx::neg(Expr a)
{
    return mul({number(keel::i64{-1}), a});
}

Expr Ctx::div(Expr a, Expr b)
{
    if (kind(b) == NodeKind::Number) {
        assert(!numberValue(b).isZero() && "division by zero constant");
        if (numberValue(b).isZero())
            return Expr(); // null in Release: no 0^-1 garbage nodes
    }
    return mul({a, pow(b, number(keel::i64{-1}))});
}

bool Ctx::smallInteger(const Rational &e, keel::i64 &n) const
{
    if (!(e.den() == BigInt(1)))
        return false;
    if (!e.num().fitsInt64(n))
        return false;
    return -kMaxFoldExp <= n && n <= kMaxFoldExp;
}

Expr Ctx::pow(Expr base, Expr exp)
{
    if (kind(exp) == NodeKind::Number) {
        const Rational &e = numberValue(exp);
        if (e.isZero())
            return one();
        if (e == Rational(keel::i64{1}))
            return base;
        if (kind(base) == NodeKind::Number &&
            numberValue(base) == Rational(keel::i64{1}))
            return one();

        keel::i64 n = 0;
        const bool isSmallInt = smallInteger(e, n);

        if (kind(base) == NodeKind::Number && isSmallInt) {
            const Rational &b = numberValue(base);
            if (n >= 0) {
                Rational r(BigInt::powUInt(b.num(), keel::as<keel::u64>(n)),
                           BigInt::powUInt(b.den(), keel::as<keel::u64>(n)));
                return number(r);
            }
            if (b.isZero()) {
                assert(!"zero raised to a negative power");
                return Expr(); // null in Release: no 0^-k garbage nodes
            }
            // b != 0, n < 0: (p/q)^n = q^|n| / p^|n|
            Rational r(BigInt::powUInt(b.den(), keel::as<keel::u64>(-n)),
                       BigInt::powUInt(b.num(), keel::as<keel::u64>(-n)));
            return number(r);
        }

        // (u^a)^n = u^(a*n) holds for integer n.
        if (kind(base) == NodeKind::Pow && isSmallInt &&
            kind(child(base, 1)) == NodeKind::Number) {
            return pow(child(base, 0), mul({exp, child(base, 1)}));
        }

        // (u*v)^n = u^n * v^n holds for integer n.
        if (kind(base) == NodeKind::Mul && isSmallInt) {
            keel::Array<Expr> parts;
            for (keel::usize i = 0; i < childCount(base); ++i)
                parts.push_back(pow(child(base, i), exp));
            return makeMul(parts);
        }
    }
    return makeNode(NodeKind::Pow, 0, {base, exp}, Rational(keel::i64{0}));
}

Expr Ctx::makeAdd(keel::ArrayRef<Expr> children)
{
    // Collect like terms: every non-number child decomposes into
    // (coefficient, term) — a canonical Mul carries its numeric constant as
    // the first child — and coefficients of equal terms sum up. Run-only
    // merging would not be canonical: y + y + 2*y would fold the two y's
    // into a 2*y that then coexists with the original 2*y child.
    keel::Array<keel::Pair<Expr, Rational>> acc;
    Rational constSum(0);
    const auto absorbTerm = [&](Expr c) {
        Rational coef(keel::i64{1});
        Expr term = c;
        if (kind(c) == NodeKind::Mul && childCount(c) > 0 &&
            kind(child(c, 0)) == NodeKind::Number) {
            coef = numberValue(child(c, 0));
            if (childCount(c) == 2) {
                term = child(c, 1);
            } else {
                keel::Array<Expr> rest;
                for (keel::usize i = 1; i < childCount(c); ++i)
                    rest.push_back(child(c, i));
                term = mul(rest);
            }
        }
        for (auto &p : acc) {
            if (p.first == term) {
                p.second += coef;
                return;
            }
        }
        acc.push_back({term, coef});
    };
    for (Expr c : children) {
        assert(!c.isNull());
        if (kind(c) == NodeKind::Number) {
            constSum += numberValue(c);
        } else if (kind(c) == NodeKind::Add) {
            // Canonical Add children are never Adds themselves.
            for (keel::usize i = 0; i < childCount(c); ++i) {
                const Expr g = child(c, i);
                if (kind(g) == NodeKind::Number)
                    constSum += numberValue(g);
                else
                    absorbTerm(g);
            }
        } else {
            absorbTerm(c);
        }
    }

    keel::Array<Expr> items;
    for (const auto &p : acc) {
        if (p.second.isZero())
            continue;
        items.push_back(p.second == Rational(keel::i64{1})
                            ? p.first
                            : mul({number(p.second), p.first}));
    }
    if (!constSum.isZero())
        items.push_back(number(constSum));

    if (items.empty())
        return zero();
    if (items.size() == 1)
        return items[0];
#ifndef NDEBUG
    for (keel::usize i = 0; i < items.size(); ++i)
        for (keel::usize j = i + 1; j < items.size(); ++j)
            assert(items[i] != items[j] && "makeAdd duplicate items");
#endif
    keel::sort(items,
               [this](Expr a, Expr b) { return compare(a, b) < 0; });
    return makeNode(NodeKind::Add, 0, items, Rational(keel::i64{0}));
}

Expr Ctx::makeMul(keel::ArrayRef<Expr> children)
{
    // Collect like bases: every non-number child decomposes into
    // (base, exponent) — Pow with a numeric exponent — and exponents of
    // equal bases sum up. Mirrors the coefficient collection of makeAdd;
    // run-only merging would leave x * x * x^2 as x^2 * x^2.
    keel::Array<keel::Pair<Expr, Rational>> acc;
    Rational constProd(1);
    const auto absorbBase = [&](Expr c) {
        Expr base = c;
        Rational exp(keel::i64{1});
        if (kind(c) == NodeKind::Pow && childCount(c) == 2 &&
            kind(child(c, 1)) == NodeKind::Number) {
            base = child(c, 0);
            exp = numberValue(child(c, 1));
        }
        for (auto &p : acc) {
            if (p.first == base) {
                p.second += exp;
                return;
            }
        }
        acc.push_back({base, exp});
    };
    for (Expr c : children) {
        assert(!c.isNull());
        if (kind(c) == NodeKind::Number) {
            constProd *= numberValue(c);
        } else if (kind(c) == NodeKind::Mul) {
            // Canonical Mul children are never Muls themselves.
            for (keel::usize i = 0; i < childCount(c); ++i) {
                const Expr g = child(c, i);
                if (kind(g) == NodeKind::Number)
                    constProd *= numberValue(g);
                else
                    absorbBase(g);
            }
        } else {
            absorbBase(c);
        }
    }
    if (constProd.isZero())
        return zero();

    keel::Array<Expr> items;
    for (const auto &p : acc) {
        if (p.second.isZero())
            continue;
        items.push_back(p.second == Rational(keel::i64{1})
                            ? p.first
                            : pow(p.first, number(p.second)));
    }
    if (!(constProd == Rational(keel::i64{1})))
        items.push_back(number(constProd));

    if (items.empty())
        return one();
    if (items.size() == 1)
        return items[0];
#ifndef NDEBUG
    for (keel::usize i = 0; i < items.size(); ++i)
        for (keel::usize j = i + 1; j < items.size(); ++j)
            assert(items[i] != items[j] && "makeMul duplicate items");
#endif
    keel::sort(items,
               [this](Expr a, Expr b) { return compare(a, b) < 0; });
    return makeNode(NodeKind::Mul, 0, items, Rational(keel::i64{0}));
}

Expr Ctx::makeNode(NodeKind kind, keel::u32 aux,
                   keel::ArrayRef<Expr> children, const Rational &num)
{
    keel::u32 hash = mix32(kFnvOffset, keel::as<keel::u32>(kind));
    hash = mix32(hash, aux);
    if (kind == NodeKind::Number) {
        const keel::u64 h64 = num.hashBits();
        hash = mix32(hash, keel::as<keel::u32>(h64));
        hash = mix32(hash, keel::as<keel::u32>(h64 >> 32));
    }
    for (Expr c : children)
        hash = mix32(hash, node(c).hash);

    if (const keel::u32 *head = internHead_.get(hash)) {
        for (keel::u32 nid = *head; nid != 0; nid = internNext_[nid - 1]) {
            const Node &n = nodes_[nid - 1];
            if (n.hash == hash &&
                equalNode(n, kind, aux, children, num))
                return Expr(this, nid);
        }
    }

    Node n;
    n.kind = kind;
    n.aux = aux;
    n.childOff = keel::as<keel::u32>(childArena_.size());
    n.childCount = keel::as<keel::u32>(children.size());
    n.hash = hash;
    n.num = num;
    for (Expr c : children)
        childArena_.push_back(c.id_);

    const auto id = keel::as<keel::u32>(nodes_.size() + 1);
    nodes_.push_back(keel::move(n));
    const keel::u32 prevHead = internHead_.get(hash) ? *internHead_.get(hash) : 0u;
    internNext_.push_back(prevHead);
    internHead_.put(hash, id);
    return Expr(this, id);
}

bool Ctx::equalNode(const Node &n, NodeKind kind, keel::u32 aux,
                    keel::ArrayRef<Expr> children, const Rational &num) const
{
    if (n.kind != kind || n.aux != aux || n.childCount != children.size())
        return false;
    if (kind == NodeKind::Number && !(n.num == num))
        return false;
    for (keel::usize i = 0; i < children.size(); ++i)
        if (childArena_[n.childOff + i] != children[i].id_)
            return false;
    return true;
}

const keel::String &Ctx::symbolName(Expr e) const
{
    assert(kind(e) == NodeKind::Symbol);
    return symbolNames_[node(e).aux];
}

const keel::String &Ctx::funcName(Expr e) const
{
    assert(kind(e) == NodeKind::Func);
    return funcNames_[node(e).aux];
}

Expr Ctx::child(Expr e, keel::usize i) const
{
    const Node &n = node(e);
    assert(i < n.childCount);
    return Expr(const_cast<Ctx *>(this), childArena_[n.childOff + i]);
}

keel::i32 Ctx::kindRank(NodeKind k)
{
    switch (k) {
    case NodeKind::Number: return 0;
    case NodeKind::Symbol: return 1;
    case NodeKind::Pow:    return 2;
    case NodeKind::Func:   return 3;
    case NodeKind::Add:    return 4;
    case NodeKind::Mul:    return 5;
    case NodeKind::RootOf: return 6;
    }
    return 7;
}

keel::i32 Ctx::compare(Expr a, Expr b) const
{
    assert(!a.isNull() && !b.isNull());
    const Node &na = node(a);
    const Node &nb = node(b);
    if (na.kind != nb.kind)
        return kindRank(na.kind) < kindRank(nb.kind) ? -1 : 1;

    switch (na.kind) {
    case NodeKind::Number:
        return na.num < nb.num ? -1 : (nb.num < na.num ? 1 : 0);
    case NodeKind::Symbol:
        return signOf(symbolNames_[na.aux].as_ref().compare(symbolNames_[nb.aux].as_ref()));
    case NodeKind::Func: {
        const keel::i32 byName = funcNames_[na.aux].as_ref().compare(funcNames_[nb.aux].as_ref());
        if (byName != 0)
            return signOf(byName);
        const keel::usize n = keel::min(na.childCount, nb.childCount);
        for (keel::usize i = 0; i < n; ++i) {
            const keel::i32 c = compare(child(a, i), child(b, i));
            if (c != 0)
                return c;
        }
        return na.childCount < nb.childCount ? -1
               : na.childCount > nb.childCount ? 1 : 0;
    }
    case NodeKind::Pow: {
        const keel::i32 byBase = compare(child(a, 0), child(b, 0));
        if (byBase != 0)
            return byBase;
        return compare(child(a, 1), child(b, 1));
    }
    case NodeKind::RootOf: {
        if (na.aux != nb.aux) {
            const RootOfDesc &da = rootofs_[na.aux];
            const RootOfDesc &db = rootofs_[nb.aux];
            const keel::usize n = keel::min(da.poly.size(), db.poly.size());
            for (keel::usize i = 0; i < n; ++i)
                if (!(da.poly[i] == db.poly[i]))
                    return da.poly[i] < db.poly[i] ? -1 : 1;
            if (da.poly.size() != db.poly.size())
                return da.poly.size() < db.poly.size() ? -1 : 1;
            return da.index < db.index ? -1 : 1;
        }
        return 0;
    }
    case NodeKind::Add:
    case NodeKind::Mul: {
        const keel::usize n = keel::min(na.childCount, nb.childCount);
        for (keel::usize i = 0; i < n; ++i) {
            const keel::i32 c = compare(child(a, i), child(b, i));
            if (c != 0)
                return c;
        }
        return na.childCount < nb.childCount ? -1
               : na.childCount > nb.childCount ? 1 : 0;
    }
    }
    return 0;
}

void Ctx::printPrec(Expr e, keel::String &out, keel::i32 parentPrec) const
{
    const Node &n = node(e);
    const keel::i32 prec = precOf(n.kind, n.num);

    switch (n.kind) {
    case NodeKind::Number:
    case NodeKind::Symbol: {
        if (prec < parentPrec)
            out.push_back('(');
        if (n.kind == NodeKind::Number)
            out.append(n.num.toString());
        else
            out.append(symbolNames_[n.aux]);
        if (prec < parentPrec)
            out.push_back(')');
        break;
    }
    case NodeKind::RootOf: {
        out.append("RootOf(");
        const RootOfDesc &d = rootofs_[n.aux];
        for (keel::usize k = d.poly.size(); k-- > 0;) {
            out.append(d.poly[k].toString());
            if (k == 1) {
                out.append("*z + ");
            } else if (k > 1) {
                keel::format_into(out, "*z^{} + ", k);
            }
        }
        keel::format_into(out, ", {})", d.index);
        break;
    }
    case NodeKind::Func: {
        if (n.childCount == 2) {
            const keel::StringRef fn = funcNames_[n.aux].as_ref();
            keel::StringRef relOp;
            if (fn == "__eq") relOp = " == ";
            else if (fn == "__ne") relOp = " ~= ";
            else if (fn == "__lt") relOp = " < ";
            else if (fn == "__le") relOp = " <= ";
            else if (fn == "__gt") relOp = " > ";
            else if (fn == "__ge") relOp = " >= ";
            if (!relOp.empty()) {
                if (parentPrec > 0)
                    out.push_back('(');
                printPrec(child(e, 0), out, 10);
                out.append(relOp);
                printPrec(child(e, 1), out, 10);
                if (parentPrec > 0)
                    out.push_back(')');
                break;
            }
        }
        if (prec < parentPrec)
            out.push_back('(');
        out.append(funcNames_[n.aux]);
        out.push_back('(');
        for (keel::usize i = 0; i < n.childCount; ++i) {
            if (i > 0)
                out.append(", ");
            printPrec(child(e, i), out, 0);
        }
        out.push_back(')');
        if (prec < parentPrec)
            out.push_back(')');
        break;
    }
    case NodeKind::Pow: {
        if (prec < parentPrec)
            out.push_back('(');
        // A NEGATIVE numeric base must keep parens: "-9^(1/2)" reads
        // back as -(9^(1/2)) under the parser's precedence (unary
        // minus looser than '^') — a different principal branch
        // (bugs/opened/core/expr-neg-pow-base-print.md).
        const bool negNumBase = kind(child(e, 0)) == NodeKind::Number &&
                                numberValue(child(e, 0)).num().isNegative();
        if (negNumBase)
            out.push_back('(');
        // 61, not 60: a Pow base that is itself a Pow must keep parens
        // ("(x^2)^3" != "x^(2^3)").
        printPrec(child(e, 0), out, negNumBase ? 0 : 61);
        if (negNumBase)
            out.push_back(')');
        out.push_back('^');
        printPrec(child(e, 1), out, 61);
        if (prec < parentPrec)
            out.push_back(')');
        break;
    }
    case NodeKind::Mul: {
        if (prec < parentPrec)
            out.push_back('(');
        keel::usize start = 0;
        if (childCount(e) > 1 && kind(child(e, 0)) == NodeKind::Number &&
            numberValue(child(e, 0)) == Rational(keel::i64{-1})) {
            out.push_back('-');
            start = 1;
        }
        for (keel::usize i = start; i < childCount(e); ++i) {
            if (i > start)
                out.push_back('*');
            printPrec(child(e, i), out, 50);
        }
        if (prec < parentPrec)
            out.push_back(')');
        break;
    }
    case NodeKind::Add: {
        if (prec < parentPrec)
            out.push_back('(');
        for (keel::usize i = 0; i < childCount(e); ++i) {
            if (i > 0)
                out.append(" + ");
            printPrec(child(e, i), out, 40);
        }
        if (prec < parentPrec)
            out.push_back(')');
        break;
    }
    }
}

void Ctx::print(Expr e, keel::String &out) const
{
    printPrec(e, out, 0);
}

namespace {

bool bernoulliExact(keel::i64 n, Rational &out)
{
    if (n < 0 || n > 60)
        return false;
    if (n == 0) {
        out = Rational(1);
        return true;
    }
    if (n == 1) {
        out = Rational(-1, BigInt(2));
        return true;
    }
    if (n % 2 != 0) {
        out = Rational(0);
        return true;
    }
    // Akiyama-Tanigawa algorithm for B_n (with B_1 = -1/2 since n >= 2 is even).
    keel::Array<Rational> a(n + 1);
    for (keel::i64 m = 0; m <= n; ++m) {
        a[keel::as<keel::usize>(m)] = Rational(1, BigInt(m + 1));
        for (keel::i64 j = m; j >= 1; --j) {
            const keel::usize idx = keel::as<keel::usize>(j - 1);
            a[idx] = Rational(j) * (a[idx] - a[idx + 1]);
        }
    }
    out = a[0];
    return true;
}

bool eulerExact(keel::i64 n, Rational &out)
{
    if (n < 0 || n > 40)
        return false;
    if (n == 0) {
        out = Rational(1);
        return true;
    }
    if (n % 2 != 0) {
        out = Rational(0);
        return true;
    }
    const keel::i64 mMax = n / 2;
    keel::Array<BigInt> eEven(mMax + 1, BigInt(0));
    eEven[0] = BigInt(1);
    for (keel::i64 m = 1; m <= mMax; ++m) {
        BigInt sum(0);
        BigInt binom(1);
        for (keel::i64 k = 0; k < m; ++k) {
            if (k > 0) {
                binom = (binom * BigInt(2 * m - 2 * k + 2) *
                         BigInt(2 * m - 2 * k + 1)) /
                        (BigInt(2 * k - 1) * BigInt(2 * k));
            }
            sum = sum + binom * eEven[keel::as<keel::usize>(k)];
        }
        eEven[keel::as<keel::usize>(m)] = -sum;
    }
    out = Rational(eEven[keel::as<keel::usize>(mMax)], BigInt(1));
    return true;
}

bool evalBernoulliPolyExact(keel::i64 n, const Rational &x, Rational &out)
{
    if (n < 0 || n > 40)
        return false;
    Rational sum(0);
    BigInt binom(1);
    for (keel::i64 k = 0; k <= n; ++k) {
        if (k > 0)
            binom = (binom * BigInt(n - k + 1)) / BigInt(k);
        Rational bk;
        if (!bernoulliExact(k, bk))
            return false;
        if (!bk.isZero()) {
            sum = sum + Rational(binom, BigInt(1)) * bk *
                            Rational::powUInt(
                                x, keel::as<keel::u64>(n - k));
        }
    }
    out = sum;
    return true;
}

bool evalEulerPolyExact(keel::i64 n, const Rational &x, Rational &out)
{
    if (n < 0 || n > 40)
        return false;
    const Rational xShift = x - Rational(1, BigInt(2));
    Rational sum(0);
    BigInt binom(1);
    for (keel::i64 k = 0; k <= n; ++k) {
        if (k > 0)
            binom = (binom * BigInt(n - k + 1)) / BigInt(k);
        Rational ek;
        if (!eulerExact(k, ek))
            return false;
        if (!ek.isZero()) {
            const BigInt twoPow =
                BigInt::powUInt(BigInt(2), keel::as<keel::usize>(k));
            sum = sum + Rational(binom, twoPow) * ek *
                            Rational::powUInt(
                                xShift, keel::as<keel::u64>(n - k));
        }
    }
    out = sum;
    return true;
}

bool evalPolylogNegIntExact(keel::i64 m, const Rational &z, Rational &out)
{
    if (m < 0 || m > 20 || z == Rational(1))
        return false;
    const Rational den =
        Rational::powUInt(Rational(1) - z, keel::as<keel::u64>(m + 1));
    if (m == 0) {
        out = z / den;
        return true;
    }
    keel::Array<BigInt> eul(m, BigInt(0));
    eul[0] = BigInt(1);
    for (keel::i64 i = 2; i <= m; ++i) {
        for (keel::i64 k = i - 1; k >= 1; --k) {
            eul[keel::as<keel::usize>(k)] =
                BigInt(k + 1) * eul[keel::as<keel::usize>(k)] +
                BigInt(i - k) * eul[keel::as<keel::usize>(k - 1)];
        }
    }
    Rational num(0);
    for (keel::i64 k = 0; k < m; ++k) {
        num = num + Rational(eul[keel::as<keel::usize>(k)], BigInt(1)) *
                        Rational::powUInt(z, keel::as<keel::u64>(m - k));
    }
    out = num / den;
    return true;
}

} // namespace

bool Ctx::evalExact(
    Expr e, keel::ArrayRef<keel::Pair<keel::StringRef, Rational>> vals,
    Rational &out)
{
    switch (kind(e)) {
    case NodeKind::Number:
        out = numberValue(e);
        return true;
    case NodeKind::Symbol: {
        const keel::String &name = symbolName(e);
        for (const auto &kv : vals)
            if (kv.first == name) {
                out = kv.second;
                return true;
            }
        return false;
    }
    case NodeKind::RootOf:
        return false; // algebraic, not rational (interval refinement
                      // is the future numeric layer's business)
    case NodeKind::Func: {
        const keel::String &name = funcName(e);
        const Rational zero(0), one(1);
        if (childCount(e) == 4 && name == "hypergeom2F1") {
            Rational aVal, bVal, cVal, zVal;
            const bool hasA = evalExact(child(e, 0), vals, aVal);
            const bool hasB = evalExact(child(e, 1), vals, bVal);
            const bool hasC = evalExact(child(e, 2), vals, cVal);
            const bool hasZ = evalExact(child(e, 3), vals, zVal);
            if (hasZ && zVal == zero) {
                out = one;
                return true;
            }
            if ((hasA && aVal == zero) || (hasB && bVal == zero)) {
                out = one;
                return true;
            }
            if (!hasA || !hasB || !hasC || !hasZ)
                return false;
            keel::i64 mTerm = -1;
            if (aVal.den() == BigInt(1) && aVal.signum() <= 0) {
                keel::i64 ma = 0;
                if (aVal.num().fitsInt64(ma) && -ma <= 40)
                    mTerm = -ma;
            }
            if (bVal.den() == BigInt(1) && bVal.signum() <= 0) {
                keel::i64 mb = 0;
                if (bVal.num().fitsInt64(mb) && -mb <= 40 &&
                    (mTerm < 0 || -mb < mTerm)) {
                    mTerm = -mb;
                }
            }
            if (mTerm >= 0) {
                Rational sum = one, term = one;
                for (keel::i64 k = 0; k < mTerm; ++k) {
                    const Rational ck = cVal + Rational(k);
                    if (ck.isZero())
                        return false;
                    term = term * (aVal + Rational(k)) * (bVal + Rational(k)) *
                           zVal / (ck * Rational(k + 1));
                    sum = sum + term;
                }
                out = sum;
                return true;
            }
            return false;
        }
        if (childCount(e) == 3 && name == "hypergeom1F1") {
            Rational aVal, bVal, zVal;
            const bool hasA = evalExact(child(e, 0), vals, aVal);
            const bool hasB = evalExact(child(e, 1), vals, bVal);
            const bool hasZ = evalExact(child(e, 2), vals, zVal);
            if ((hasZ && zVal == zero) || (hasA && aVal == zero)) {
                out = one;
                return true;
            }
            if (!hasA || !hasB || !hasZ)
                return false;
            keel::i64 ma = 0;
            if (aVal.den() == BigInt(1) && aVal.signum() <= 0 &&
                aVal.num().fitsInt64(ma) && -ma <= 40) {
                const keel::i64 mTerm = -ma;
                Rational sum = one, term = one;
                for (keel::i64 k = 0; k < mTerm; ++k) {
                    const Rational bk = bVal + Rational(k);
                    if (bk.isZero())
                        return false;
                    term = term * (aVal + Rational(k)) * zVal /
                           (bk * Rational(k + 1));
                    sum = sum + term;
                }
                out = sum;
                return true;
            }
            return false;
        }
        if (childCount(e) == 2) {
            Rational nVal, xVal;
            const bool hasN = evalExact(child(e, 0), vals, nVal);
            const bool hasX = evalExact(child(e, 1), vals, xVal);
            if (name == "polylog" && hasX && xVal == zero) {
                out = zero;
                return true;
            }
            if (name == "hypergeom0F1" && hasX && xVal == zero) {
                out = one;
                return true;
            }
            if (name == "gammainc" && hasX && xVal == zero &&
                (!hasN || nVal > zero)) {
                out = zero;
                return true;
            }
            if (name == "igamma" && hasN && hasX && xVal == zero &&
                nVal.den() == BigInt(1) && nVal > zero) {
                keel::i64 nInt = 0;
                if (nVal.num().fitsInt64(nInt) && nInt >= 1 && nInt <= 30) {
                    BigInt fact(1);
                    for (keel::i64 k = 2; k < nInt; ++k)
                        fact = fact * BigInt(k);
                    out = Rational(fact, BigInt(1));
                    return true;
                }
            }
            if (name == "pochhammer" && hasX && xVal == zero) {
                out = one;
                return true;
            }
            if (!hasN)
                return false;
            if (name == "pochhammer" && hasX && xVal.den() == BigInt(1)) {
                keel::i64 kCount = 0;
                if (xVal.num().fitsInt64(kCount) && kCount >= 0 &&
                    kCount <= 40) {
                    Rational prod = one;
                    for (keel::i64 j = 0; j < kCount; ++j)
                        prod = prod * (nVal + Rational(j));
                    out = prod;
                    return true;
                }
                return false;
            }
            if ((name == "stirlingS1" || name == "stirlingS2") && hasX &&
                nVal.den() == BigInt(1) && xVal.den() == BigInt(1)) {
                keel::i64 nInt = 0, kInt = 0;
                if (nVal.num().fitsInt64(nInt) && xVal.num().fitsInt64(kInt) &&
                    nInt >= 0 && nInt <= 50) {
                    if (kInt < 0 || kInt > nInt) {
                        out = zero;
                        return true;
                    }
                    if (nInt == 0 && kInt == 0) {
                        out = one;
                        return true;
                    }
                    if (kInt == 0) {
                        out = zero;
                        return true;
                    }
                    keel::Array<BigInt> row(kInt + 1,
                                            BigInt(0));
                    row[0] = BigInt(1);
                    for (keel::i64 i = 1; i <= nInt; ++i) {
                        const keel::i64 jMax = keel::min(i, kInt);
                        for (keel::i64 j = jMax; j >= 1; --j) {
                            const auto ju = keel::as<keel::usize>(j);
                            if (name == "stirlingS1") {
                                row[ju] = row[ju - 1] - BigInt(i - 1) * row[ju];
                            } else {
                                row[ju] = BigInt(j) * row[ju] + row[ju - 1];
                            }
                        }
                        row[0] = BigInt(0);
                    }
                    out = Rational(row[keel::as<keel::usize>(kInt)], BigInt(1));
                    return true;
                }
                return false;
            }
            if (name == "beta" && hasX && nVal.den() == BigInt(1) &&
                xVal.den() == BigInt(1)) {
                keel::i64 mInt = 0, kInt = 0;
                if (nVal.num().fitsInt64(mInt) && xVal.num().fitsInt64(kInt) &&
                    mInt >= 1 && kInt >= 1 && mInt + kInt <= 50) {
                    BigInt fM(1), fK(1), fMK(1);
                    for (keel::i64 j = 2; j < mInt; ++j)
                        fM = fM * BigInt(j);
                    for (keel::i64 j = 2; j < kInt; ++j)
                        fK = fK * BigInt(j);
                    for (keel::i64 j = 2; j < mInt + kInt; ++j)
                        fMK = fMK * BigInt(j);
                    out = Rational(fM * fK, fMK);
                    return true;
                }
                return false;
            }
            if (name == "ellipticF" || name == "ellipticEInc" ||
                name == "ellipticE") {
                if (nVal == zero) {
                    out = zero;
                    return true;
                }
                if (hasX && xVal == zero) {
                    out = nVal;
                    return true;
                }
                return false;
            }
            if ((name == "besselj" || name == "besseli") && hasX &&
                xVal == zero) {
                if (nVal == zero) {
                    out = one;
                    return true;
                }
                if (nVal > zero) {
                    out = zero;
                    return true;
                }
                return false;
            }
            if (!hasX)
                return false;
            keel::i64 n = 0;
            if (!(nVal.den() == BigInt(1)) || !nVal.num().fitsInt64(n))
                return false;
            if (name == "legendreP") {
                if (n < 0)
                    n = -n - 1;
                if (n > 64)
                    return false;
                if (n == 0) { out = one; return true; }
                if (n == 1) { out = xVal; return true; }
                Rational pPrev = one, pCur = xVal;
                for (keel::i64 k = 1; k < n; ++k) {
                    const Rational pNext =
                        (Rational(2 * k + 1) * xVal * pCur -
                         Rational(k) * pPrev) /
                        Rational(k + 1);
                    pPrev = pCur;
                    pCur = pNext;
                }
                out = pCur;
                return true;
            }
            if (name == "chebyshevT") {
                if (n < 0)
                    n = -n;
                if (n > 64)
                    return false;
                if (n == 0) { out = one; return true; }
                if (n == 1) { out = xVal; return true; }
                Rational tPrev = one, tCur = xVal;
                for (keel::i64 k = 1; k < n; ++k) {
                    const Rational tNext =
                        Rational(2) * xVal * tCur - tPrev;
                    tPrev = tCur;
                    tCur = tNext;
                }
                out = tCur;
                return true;
            }
            if (name == "chebyshevU") {
                Rational sgn = one;
                if (n == -1) { out = zero; return true; }
                if (n < -1) {
                    n = -n - 2;
                    sgn = Rational(-1);
                }
                if (n > 64)
                    return false;
                if (n == 0) { out = sgn; return true; }
                if (n == 1) { out = sgn * Rational(2) * xVal; return true; }
                Rational uPrev = one, uCur = Rational(2) * xVal;
                for (keel::i64 k = 1; k < n; ++k) {
                    const Rational uNext =
                        Rational(2) * xVal * uCur - uPrev;
                    uPrev = uCur;
                    uCur = uNext;
                }
                out = sgn * uCur;
                return true;
            }
            if (name == "hermiteH") {
                if (n < 0 || n > 64)
                    return false;
                if (n == 0) { out = one; return true; }
                if (n == 1) { out = Rational(2) * xVal; return true; }
                Rational hPrev = one, hCur = Rational(2) * xVal;
                for (keel::i64 k = 1; k < n; ++k) {
                    const Rational hNext =
                        Rational(2) * xVal * hCur -
                        Rational(2 * k) * hPrev;
                    hPrev = hCur;
                    hCur = hNext;
                }
                out = hCur;
                return true;
            }
            if (name == "laguerreL") {
                if (n < 0 || n > 64)
                    return false;
                if (n == 0) { out = one; return true; }
                if (n == 1) { out = one - xVal; return true; }
                Rational lPrev = one, lCur = one - xVal;
                for (keel::i64 k = 1; k < n; ++k) {
                    const Rational lNext =
                        ((Rational(2 * k + 1) - xVal) * lCur -
                         Rational(k) * lPrev) /
                        Rational(k + 1);
                    lPrev = lCur;
                    lCur = lNext;
                }
                out = lCur;
                return true;
            }
            if (name == "bernoulliB")
                return evalBernoulliPolyExact(n, xVal, out);
            if (name == "eulerE")
                return evalEulerPolyExact(n, xVal, out);
            if (name == "polylog" && n <= 0)
                return evalPolylogNegIntExact(-n, xVal, out);
            return false;
        }
        Rational a;
        if (!evalExact(child(e, 0), vals, a))
            return false;
        if (name == "bernoulliB" && a.den() == BigInt(1)) {
            keel::i64 k = 0;
            if (a.num().fitsInt64(k))
                return bernoulliExact(k, out);
            return false;
        }
        if (name == "eulerE" && a.den() == BigInt(1)) {
            keel::i64 k = 0;
            if (a.num().fitsInt64(k))
                return eulerExact(k, out);
            return false;
        }
        if (name == "zeta" && a.den() == BigInt(1)) {
            keel::i64 s = 0;
            if (a.num().fitsInt64(s) && s <= 0 && s >= -59) {
                if (s == 0) {
                    out = Rational(-1, BigInt(2));
                    return true;
                }
                const keel::i64 m = -s;
                Rational bVal;
                if (!bernoulliExact(m + 1, bVal))
                    return false;
                const Rational sgn(m % 2 == 0 ? 1 : -1);
                out = sgn * bVal / Rational(m + 1);
                return true;
            }
            return false;
        }
        if (name == "dirichletEta" && a.den() == BigInt(1)) {
            keel::i64 s = 0;
            if (a.num().fitsInt64(s) && s <= 0 && s >= -59) {
                if (s == 0) {
                    out = Rational(1, BigInt(2));
                    return true;
                }
                const keel::i64 m = -s;
                Rational bVal;
                if (!bernoulliExact(m + 1, bVal))
                    return false;
                const BigInt twoPow =
                    BigInt::powUInt(BigInt(2), keel::as<keel::usize>(m + 1));
                const Rational sgn(m % 2 == 0 ? -1 : 1);
                out = sgn * Rational(twoPow - BigInt(1), BigInt(m + 1)) * bVal;
                return true;
            }
            return false;
        }
        if (name == "sqrt" && (a == zero || a == one)) { out = a; return true; }
        if (name == "exp" && a == zero) { out = one; return true; }
        if (name == "log" && a == one) { out = zero; return true; }
        if ((name == "sin" || name == "tan" || name == "atan" ||
             name == "asin" || name == "sinh" || name == "tanh" ||
             name == "asinh" || name == "atanh" || name == "erf" ||
             name == "erfi" || name == "li" || name == "Si" ||
             name == "FresnelS" || name == "FresnelC" || name == "dilog" ||
             name == "Li2" || name == "polylog2") &&
            a == zero) {
            out = zero;
            return true;
        }
        if ((name == "cos" || name == "cosh" || name == "sec" ||
             name == "sech" || name == "erfc") &&
            a == zero) {
            out = one;
            return true;
        }
        if ((name == "acos" || name == "acosh") && a == one) {
            out = zero;
            return true;
        }
        if (name == "factorial" && a.den() == BigInt(1)) {
            keel::i64 k = 0;
            if (a.num().fitsInt64(k) && k >= 0 && k <= 30) {
                BigInt fact(1);
                for (keel::i64 i = 2; i <= k; ++i)
                    fact = fact * BigInt(i);
                out = Rational(fact, BigInt(1));
                return true;
            }
        }
        if (name == "gamma" && a.den() == BigInt(1)) {
            keel::i64 k = 0;
            if (a.num().fitsInt64(k) && k >= 1 && k <= 31) {
                BigInt fact(1);
                for (keel::i64 i = 2; i <= k - 1; ++i)
                    fact = fact * BigInt(i);
                out = Rational(fact, BigInt(1));
                return true;
            }
        }
        if ((name == "lgamma" || name == "loggamma") &&
            (a == one || a == Rational(keel::i64{2}))) {
            out = zero;
            return true;
        }
        if (name == "ellipticE" && a == one) {
            out = one;
            return true;
        }
        return false;
    }
    case NodeKind::Pow: {
        Rational base, ex;
        if (!evalExact(child(e, 0), vals, base) ||
            !evalExact(child(e, 1), vals, ex))
            return false;
        keel::i64 k = 0;
        if (!(ex.den() == BigInt(1)) || !ex.num().fitsInt64(k))
            return false; // fractional or huge exponent: irrational
        if (k >= 0) {
            out = Rational::powUInt(base, keel::as<keel::u64>(k));
            return true;
        }
        if (base.isZero())
            return false; // 0^negative
        out = Rational(BigInt(1), BigInt(1)) /
              Rational::powUInt(base, keel::as<keel::u64>(-k));
        return true;
    }
    case NodeKind::Add:
    case NodeKind::Mul: {
        Rational acc = kind(e) == NodeKind::Add
                           ? Rational(keel::i64{0})
                           : Rational(keel::i64{1});
        for (keel::usize i = 0; i < childCount(e); ++i) {
            Rational t;
            if (!evalExact(child(e, i), vals, t))
                return false;
            acc = kind(e) == NodeKind::Add ? acc + t : acc * t;
        }
        out = acc;
        return true;
    }
    }
    return false;
}

namespace {

constexpr keel::f64 kPiDouble = keel::kPi;
constexpr keel::f64 kEulerGamma = keel::kEulerGamma;

keel::f64 evalErfiDouble(keel::f64 x)
{
    if (x == 0.0)
        return 0.0;
    const keel::f64 sgn = x < 0.0 ? -1.0 : 1.0;
    const keel::f64 ax = keel::abs(x);
    if (ax > 26.5)
        return sgn * keel::kInf;
    const keel::f64 x2 = ax * ax;
    keel::f64 term = ax;
    keel::f64 sum = term;
    for (keel::i32 n = 1; n <= 200; ++n) {
        term *= x2 / keel::as<keel::f64>(n);
        const keel::f64 contrib = term / keel::as<keel::f64>(2 * n + 1);
        sum += contrib;
        if (contrib <= sum * 1e-16)
            break;
    }
    return sgn * (2.0 / keel::sqrt(kPiDouble)) * sum;
}

bool evalEiDouble(keel::f64 x, keel::f64 &out)
{
    if (x == 0.0)
        return false;
    if (x > 0.0) {
        if (x > 700.0)
            return false;
        keel::f64 sum = 0.0;
        keel::f64 term = 1.0;
        for (keel::i32 n = 1; n <= 300; ++n) {
            term *= x / keel::as<keel::f64>(n);
            const keel::f64 contrib = term / keel::as<keel::f64>(n);
            sum += contrib;
            if (contrib <= sum * 1e-16 && n > x)
                break;
        }
        out = kEulerGamma + keel::log(x) + sum;
        return keel::is_finite(out);
    }
    const keel::f64 z = -x;
    if (z <= 4.0) {
        keel::f64 sum = 0.0;
        keel::f64 term = 1.0;
        for (keel::i32 n = 1; n <= 120; ++n) {
            term *= x / keel::as<keel::f64>(n);
            const keel::f64 contrib = term / keel::as<keel::f64>(n);
            sum += contrib;
            if (keel::abs(contrib) <= 1e-16)
                break;
        }
        out = kEulerGamma + keel::log(z) + sum;
        return keel::is_finite(out);
    }
    // Continued fraction for E_1(z) (z > 4):
    // E_1(z) = exp(-z) / (z + 1/(1 + 1/(z + 2/(1 + 2/(z + ...)))))
    keel::f64 b = z + 1.0;
    keel::f64 c = 1.0 / 1e-30;
    keel::f64 d = 1.0 / b;
    keel::f64 h = d;
    for (keel::i32 i = 1; i <= 100; ++i) {
        const keel::f64 a = -keel::as<keel::f64>(i * i);
        b += 2.0;
        d = a * d + b;
        if (keel::abs(d) < 1e-30)
            d = 1e-30;
        c = b + a / c;
        if (keel::abs(c) < 1e-30)
            c = 1e-30;
        d = 1.0 / d;
        const keel::f64 del = d * c;
        h *= del;
        if (keel::abs(del - 1.0) <= 1e-16)
            break;
    }
    out = -keel::exp(-z) * h;
    return keel::is_finite(out);
}

// 8-point Gauss-Legendre quadrature on [a, b].
template <typename Fn>
keel::f64 gauss8Integrate(Fn &&fn, keel::f64 a, keel::f64 b, keel::i32 panels)
{
    static constexpr keel::f64 kNodes[4] = {
        0.183434642495649805, 0.525532409916328986,
        0.796666477413626740, 0.960289856497536232};
    static constexpr keel::f64 kWeights[4] = {
        0.362683783378361983, 0.313706645877887287,
        0.222381034453374471, 0.101228536290376259};
    const keel::f64 h = (b - a) / keel::as<keel::f64>(panels);
    keel::f64 total = 0.0;
    for (keel::i32 p = 0; p < panels; ++p) {
        const keel::f64 x0 = a + p * h;
        const keel::f64 mid = x0 + 0.5 * h;
        const keel::f64 half = 0.5 * h;
        keel::f64 sub = 0.0;
        for (keel::i32 i = 0; i < 4; ++i) {
            const keel::f64 dx = half * kNodes[i];
            sub += kWeights[i] * (fn(mid - dx) + fn(mid + dx));
        }
        total += half * sub;
    }
    return total;
}

keel::f64 evalSiDouble(keel::f64 x)
{
    if (x == 0.0)
        return 0.0;
    const keel::f64 sgn = x < 0.0 ? -1.0 : 1.0;
    const keel::f64 ax = keel::abs(x);
    if (ax <= 4.0) {
        const keel::f64 x2 = ax * ax;
        keel::f64 term = ax;
        keel::f64 sum = term;
        for (keel::i32 n = 1; n <= 50; ++n) {
            term *= -x2 / keel::as<keel::f64>((2 * n) * (2 * n + 1));
            const keel::f64 contrib = term / keel::as<keel::f64>(2 * n + 1);
            sum += contrib;
            if (keel::abs(contrib) <= 1e-16)
                break;
        }
        return sgn * sum;
    }
    if (ax <= 32.0) {
        const keel::f64 si4 = evalSiDouble(4.0);
        const keel::i32 panels = keel::max(8, keel::as<keel::i32>(keel::ceil((ax - 4.0) * 2.0)));
        const keel::f64 tail = gauss8Integrate(
            [](keel::f64 t) { return keel::sin(t) / t; }, 4.0, ax, panels);
        return sgn * (si4 + tail);
    }
    // Asymptotic expansion via f(z), g(z) for z > 32.
    const keel::f64 invZ2 = 1.0 / (ax * ax);
    keel::f64 fSum = 1.0, gSum = 1.0;
    keel::f64 fTerm = 1.0, gTerm = 1.0;
    for (keel::i32 k = 1; k <= 12; ++k) {
        fTerm *= -keel::as<keel::f64>((2 * k - 1) * (2 * k)) * invZ2;
        if (keel::abs(fTerm) > 1e-3 && k > 4)
            break;
        fSum += fTerm;
        gTerm *= -keel::as<keel::f64>((2 * k) * (2 * k + 1)) * invZ2;
        gSum += gTerm;
    }
    const keel::f64 fVal = fSum / ax;
    const keel::f64 gVal = gSum * invZ2;
    return sgn * (0.5 * kPiDouble - fVal * keel::cos(ax) - gVal * keel::sin(ax));
}

bool evalCiDouble(keel::f64 x, keel::f64 &out)
{
    if (x <= 0.0)
        return false;
    if (x <= 4.0) {
        const keel::f64 x2 = x * x;
        keel::f64 term = 1.0;
        keel::f64 sum = 0.0;
        for (keel::i32 n = 1; n <= 50; ++n) {
            term *= -x2 / keel::as<keel::f64>((2 * n - 1) * (2 * n));
            const keel::f64 contrib = term / keel::as<keel::f64>(2 * n);
            sum += contrib;
            if (keel::abs(contrib) <= 1e-16)
                break;
        }
        out = kEulerGamma + keel::log(x) + sum;
        return keel::is_finite(out);
    }
    if (x <= 32.0) {
        keel::f64 ci4 = 0.0;
        evalCiDouble(4.0, ci4);
        const keel::i32 panels = keel::max(8, keel::as<keel::i32>(keel::ceil((x - 4.0) * 2.0)));
        const keel::f64 tail = gauss8Integrate(
            [](keel::f64 t) { return keel::cos(t) / t; }, 4.0, x, panels);
        out = ci4 + tail;
        return keel::is_finite(out);
    }
    const keel::f64 invZ2 = 1.0 / (x * x);
    keel::f64 fSum = 1.0, gSum = 1.0;
    keel::f64 fTerm = 1.0, gTerm = 1.0;
    for (keel::i32 k = 1; k <= 12; ++k) {
        fTerm *= -keel::as<keel::f64>((2 * k - 1) * (2 * k)) * invZ2;
        if (keel::abs(fTerm) > 1e-3 && k > 4)
            break;
        fSum += fTerm;
        gTerm *= -keel::as<keel::f64>((2 * k) * (2 * k + 1)) * invZ2;
        gSum += gTerm;
    }
    const keel::f64 fVal = fSum / x;
    const keel::f64 gVal = gSum * invZ2;
    out = fVal * keel::sin(x) - gVal * keel::cos(x);
    return keel::is_finite(out);
}

keel::f64 evalFresnelDouble(keel::f64 x, bool isSine)
{
    if (x == 0.0)
        return 0.0;
    const keel::f64 sgn = x < 0.0 ? -1.0 : 1.0;
    const keel::f64 ax = keel::abs(x);
    if (ax <= 2.5) {
        const keel::f64 halfPi = 0.5 * kPiDouble;
        const keel::f64 x2 = ax * ax;
        const keel::f64 x4 = x2 * x2;
        if (isSine) {
            keel::f64 term = halfPi * ax * x2;
            keel::f64 sum = term / 3.0;
            for (keel::i32 n = 1; n <= 45; ++n) {
                term *= -(halfPi * halfPi * x4) /
                        keel::as<keel::f64>((2 * n) * (2 * n + 1));
                const keel::f64 contrib = term / keel::as<keel::f64>(4 * n + 3);
                sum += contrib;
                if (keel::abs(contrib) <= 1e-16)
                    break;
            }
            return sgn * sum;
        }
        keel::f64 term = ax;
        keel::f64 sum = term;
        for (keel::i32 n = 1; n <= 45; ++n) {
            term *= -(halfPi * halfPi * x4) /
                    keel::as<keel::f64>((2 * n - 1) * (2 * n));
            const keel::f64 contrib = term / keel::as<keel::f64>(4 * n + 1);
            sum += contrib;
            if (keel::abs(contrib) <= 1e-16)
                break;
        }
        return sgn * sum;
    }
    if (ax <= 12.0) {
        const keel::f64 base = evalFresnelDouble(2.5, isSine);
        const keel::i32 panels = keel::max(16, keel::as<keel::i32>(keel::ceil((ax * ax - 6.25) * 4.0)));
        const keel::f64 tail = gauss8Integrate(
            [isSine](keel::f64 t) {
                const keel::f64 arg = 0.5 * kPiDouble * t * t;
                return isSine ? keel::sin(arg) : keel::cos(arg);
            },
            2.5, ax, panels);
        return sgn * (base + tail);
    }
    // Asymptotic expansion for ax > 12.
    const keel::f64 z = 0.5 * kPiDouble * ax * ax;
    const keel::f64 invPiAx = 1.0 / (kPiDouble * ax);
    const keel::f64 inv2Z = 1.0 / (2.0 * z);
    const keel::f64 fVal = invPiAx * (1.0 - 3.0 * inv2Z * inv2Z);
    const keel::f64 gVal = invPiAx * inv2Z * (1.0 - 15.0 * inv2Z * inv2Z);
    if (isSine)
        return sgn * (0.5 - fVal * keel::cos(z) - gVal * keel::sin(z));
    return sgn * (0.5 + fVal * keel::sin(z) - gVal * keel::cos(z));
}

bool evalDilogDouble(keel::f64 x, keel::f64 &out)
{
    if (!keel::is_finite(x) || x > 1.0)
        return false;
    if (x == 0.0) {
        out = 0.0;
        return true;
    }
    const keel::f64 pi2Over6 = (kPiDouble * kPiDouble) / 6.0;
    if (x == 1.0) {
        out = pi2Over6;
        return true;
    }
    if (x == -1.0) {
        out = -0.5 * pi2Over6;
        return true;
    }
    if (x < -1.0) {
        keel::f64 sub = 0.0;
        if (!evalDilogDouble(1.0 / x, sub))
            return false;
        const keel::f64 lnx = keel::log(-x);
        out = -sub - pi2Over6 - 0.5 * lnx * lnx;
        return keel::is_finite(out);
    }
    if (x < -0.5) {
        keel::f64 sub = 0.0;
        if (!evalDilogDouble(x / (x - 1.0), sub))
            return false;
        const keel::f64 ln1mx = keel::log(1.0 - x);
        out = -sub - 0.5 * ln1mx * ln1mx;
        return keel::is_finite(out);
    }
    if (x > 0.5) {
        keel::f64 sub = 0.0;
        if (!evalDilogDouble(1.0 - x, sub))
            return false;
        out = pi2Over6 - keel::log(x) * keel::log(1.0 - x) - sub;
        return keel::is_finite(out);
    }
    keel::f64 sum = 0.0;
    keel::f64 xPow = x;
    for (keel::i32 k = 1; k <= 60; ++k) {
        const keel::f64 kd = keel::as<keel::f64>(k);
        const keel::f64 contrib = xPow / (kd * kd);
        sum += contrib;
        if (keel::abs(contrib) <= 1e-16 * keel::abs(sum))
            break;
        xPow *= x;
    }
    out = sum;
    return keel::is_finite(out);
}

bool evalDigammaDouble(keel::f64 x, keel::f64 &out)
{
    if (!keel::is_finite(x))
        return false;
    if (x <= 0.0) {
        if (keel::floor(x) == x)
            return false;
        keel::f64 sub = 0.0;
        if (!evalDigammaDouble(1.0 - x, sub))
            return false;
        const keel::f64 r = x - keel::floor(x);
        const keel::f64 s = keel::sin(kPiDouble * r);
        if (s == 0.0)
            return false;
        out = sub - kPiDouble * (keel::cos(kPiDouble * r) / s);
        return keel::is_finite(out);
    }
    keel::f64 shift = 0.0;
    while (x < 10.0) {
        shift -= 1.0 / x;
        x += 1.0;
    }
    const keel::f64 invX = 1.0 / x;
    const keel::f64 invX2 = invX * invX;
    // psi(x) ~ ln(x) - 1/(2x) - sum_{k=1}^7 B_{2k}/(2k * x^{2k})
    const keel::f64 poly =
        (1.0 / 12.0) +
        invX2 *
            ((-1.0 / 120.0) +
             invX2 *
                 ((1.0 / 252.0) +
                  invX2 *
                      ((-1.0 / 240.0) +
                       invX2 *
                           ((1.0 / 132.0) +
                            invX2 * ((-691.0 / 32760.0) +
                                     invX2 * (1.0 / 12.0))))));
    out = shift + keel::log(x) - 0.5 * invX - invX2 * poly;
    return keel::is_finite(out);
}

bool evalTrigammaDouble(keel::f64 x, keel::f64 &out)
{
    if (!keel::is_finite(x))
        return false;
    if (x <= 0.0) {
        if (keel::floor(x) == x)
            return false;
        keel::f64 sub = 0.0;
        if (!evalTrigammaDouble(1.0 - x, sub))
            return false;
        const keel::f64 r = x - keel::floor(x);
        const keel::f64 s = keel::sin(kPiDouble * r);
        if (s == 0.0)
            return false;
        out = (kPiDouble * kPiDouble) / (s * s) - sub;
        return keel::is_finite(out);
    }
    keel::f64 shift = 0.0;
    while (x < 10.0) {
        shift += 1.0 / (x * x);
        x += 1.0;
    }
    const keel::f64 invX = 1.0 / x;
    const keel::f64 invX2 = invX * invX;
    // psi_1(x) ~ 1/x + 1/(2x^2) + sum_{k=1}^6 B_{2k}/x^{2k+1}
    const keel::f64 poly =
        (1.0 / 6.0) +
        invX2 *
            ((-1.0 / 30.0) +
             invX2 *
                 ((1.0 / 42.0) +
                  invX2 *
                      ((-1.0 / 30.0) +
                       invX2 * ((5.0 / 66.0) + invX2 * (-691.0 / 2730.0)))));
    out = shift + invX + 0.5 * invX2 + (invX * invX2) * poly;
    return keel::is_finite(out);
}

bool evalBesselJDouble(keel::f64 nu, keel::f64 x, keel::f64 &out)
{
    if (!keel::is_finite(nu) || !keel::is_finite(x))
        return false;
    const bool isIntNu = (keel::floor(nu) == nu);
    if (x == 0.0) {
        if (nu == 0.0) { out = 1.0; return true; }
        if (nu > 0.0) { out = 0.0; return true; }
        return false;
    }
    keel::f64 signFactor = 1.0;
    if (isIntNu && nu < 0.0) {
        const keel::i64 nInt = keel::as<keel::i64>(-nu);
        if (nInt % 2 != 0)
            signFactor = -signFactor;
        nu = -nu;
    }
    if (x < 0.0) {
        if (!isIntNu)
            return false;
        const keel::i64 nInt = keel::as<keel::i64>( keel::abs(nu) );
        if (nInt % 2 != 0)
            signFactor = -signFactor;
        x = -x;
    }
    if (x <= 12.0 + 0.5 * keel::abs(nu)) {
        const keel::f64 halfX = 0.5 * x;
        const keel::f64 halfX2 = halfX * halfX;
        keel::f64 sum = 0.0;
        if (nu >= 0.0) {
            keel::f64 term = keel::exp(nu * keel::log(halfX) - keel::lgamma(nu + 1.0));
            sum = term;
            for (keel::i32 k = 1; k <= 160; ++k) {
                term *= -halfX2 / (keel::as<keel::f64>(k) * (nu + keel::as<keel::f64>(k)));
                sum += term;
                if (keel::abs(term) <= keel::abs(sum) * 1e-16 && k > halfX)
                    break;
            }
        } else {
            for (keel::i32 k = 0; k <= 160; ++k) {
                const keel::f64 gArg = nu + keel::as<keel::f64>(k) + 1.0;
                const keel::f64 gam = keel::tgamma(gArg);
                if (!keel::is_finite(gam) || gam == 0.0)
                    continue;
                keel::f64 kFact = keel::tgamma(keel::as<keel::f64>(k) + 1.0);
                keel::f64 term = ((k % 2 == 0) ? 1.0 : -1.0) *
                              keel::pow(halfX, 2.0 * k + nu) / (kFact * gam);
                sum += term;
                if (k > 10 && keel::abs(term) <= keel::abs(sum) * 1e-16 && k > halfX)
                    break;
            }
        }
        out = signFactor * sum;
        return keel::is_finite(out);
    }
    // Hankel asymptotic expansion for x > 12 + 0.5*|nu|
    const keel::f64 mu = 4.0 * nu * nu;
    const keel::f64 chi = x - (0.5 * nu + 0.25) * kPiDouble;
    keel::f64 P = 1.0, Q = 0.0;
    keel::f64 aTerm = 1.0;
    for (keel::i32 m = 1; m <= 24; ++m) {
        const keel::f64 num = mu - keel::as<keel::f64>((2 * m - 1) * (2 * m - 1));
        const keel::f64 nextA = aTerm * num / (keel::as<keel::f64>(m) * 8.0 * x);
        if (m > 4 && keel::abs(nextA) > keel::abs(aTerm))
            break;
        aTerm = nextA;
        if (m % 2 == 1) {
            const keel::f64 sgn = ((m / 2) % 2 == 0) ? 1.0 : -1.0;
            Q += sgn * aTerm;
        } else {
            const keel::f64 sgn = ((m / 2) % 2 == 0) ? 1.0 : -1.0;
            P += sgn * aTerm;
        }
        if (keel::abs(aTerm) < 1e-16)
            break;
    }
    out = signFactor * keel::sqrt(2.0 / (kPiDouble * x)) *
          (P * keel::cos(chi) - Q * keel::sin(chi));
    return keel::is_finite(out);
}

bool evalBesselYDouble(keel::f64 nu, keel::f64 x, keel::f64 &out)
{
    if (!keel::is_finite(nu) || !keel::is_finite(x) || x <= 0.0)
        return false;
    if (x > 12.0 + 0.5 * keel::abs(nu)) {
        const keel::f64 mu = 4.0 * nu * nu;
        const keel::f64 chi = x - (0.5 * nu + 0.25) * kPiDouble;
        keel::f64 P = 1.0, Q = 0.0;
        keel::f64 aTerm = 1.0;
        for (keel::i32 m = 1; m <= 24; ++m) {
            const keel::f64 num = mu - keel::as<keel::f64>((2 * m - 1) * (2 * m - 1));
            const keel::f64 nextA = aTerm * num / (keel::as<keel::f64>(m) * 8.0 * x);
            if (m > 4 && keel::abs(nextA) > keel::abs(aTerm))
                break;
            aTerm = nextA;
            if (m % 2 == 1) {
                const keel::f64 sgn = ((m / 2) % 2 == 0) ? 1.0 : -1.0;
                Q += sgn * aTerm;
            } else {
                const keel::f64 sgn = ((m / 2) % 2 == 0) ? 1.0 : -1.0;
                P += sgn * aTerm;
            }
            if (keel::abs(aTerm) < 1e-16)
                break;
        }
        out = keel::sqrt(2.0 / (kPiDouble * x)) *
              (P * keel::sin(chi) + Q * keel::cos(chi));
        return keel::is_finite(out);
    }
    if (keel::floor(nu) != nu) {
        keel::f64 jPos = 0.0, jNeg = 0.0;
        if (!evalBesselJDouble(nu, x, jPos) || !evalBesselJDouble(-nu, x, jNeg))
            return false;
        out = (jPos * keel::cos(nu * kPiDouble) - jNeg) / keel::sin(nu * kPiDouble);
        return keel::is_finite(out);
    }
    keel::f64 signFactor = 1.0;
    keel::i32 n = keel::as<keel::i32>(nu);
    if (n < 0) {
        n = -n;
        if (n % 2 != 0)
            signFactor = -1.0;
    }
    if (n > 30)
        return false;
    keel::f64 jn = 0.0;
    if (!evalBesselJDouble(keel::as<keel::f64>(n), x, jn))
        return false;
    const keel::f64 halfX = 0.5 * x;
    const keel::f64 halfX2 = halfX * halfX;
    keel::f64 poleSum = 0.0;
    for (keel::i32 k = 0; k < n; ++k) {
        const keel::f64 numFact = keel::tgamma(keel::as<keel::f64>(n - k));
        const keel::f64 denFact = keel::tgamma(keel::as<keel::f64>(k + 1));
        poleSum += (numFact / denFact) * keel::pow(halfX, 2 * k - n);
    }
    keel::f64 hN = 0.0;
    for (keel::i32 j = 1; j <= n; ++j)
        hN += 1.0 / keel::as<keel::f64>(j);
    keel::f64 hK = 0.0;
    keel::f64 powTerm = keel::pow(halfX, n) / keel::tgamma(keel::as<keel::f64>(n + 1));
    keel::f64 regSum = (hK + hN) * powTerm;
    for (keel::i32 k = 1; k <= 120; ++k) {
        hK += 1.0 / keel::as<keel::f64>(k);
        hN += 1.0 / keel::as<keel::f64>(n + k);
        powTerm *= -halfX2 / (keel::as<keel::f64>(k) * keel::as<keel::f64>(n + k));
        const keel::f64 contrib = (hK + hN) * powTerm;
        regSum += contrib;
        if (keel::abs(contrib) <= keel::abs(regSum) * 1e-16 && k > halfX)
            break;
    }
    out = signFactor *
          ((2.0 / kPiDouble) * (keel::log(halfX) + kEulerGamma) * jn -
           (poleSum + regSum) / kPiDouble);
    return keel::is_finite(out);
}

bool evalBesselIDouble(keel::f64 nu, keel::f64 x, keel::f64 &out)
{
    if (!keel::is_finite(nu) || !keel::is_finite(x))
        return false;
    const bool isIntNu = (keel::floor(nu) == nu);
    if (x == 0.0) {
        if (nu == 0.0) { out = 1.0; return true; }
        if (nu > 0.0) { out = 0.0; return true; }
        return false;
    }
    if (isIntNu && nu < 0.0)
        nu = -nu;
    keel::f64 signFactor = 1.0;
    if (x < 0.0) {
        if (!isIntNu)
            return false;
        const keel::i64 nInt = keel::as<keel::i64>(keel::abs(nu));
        if (nInt % 2 != 0)
            signFactor = -1.0;
        x = -x;
    }
    if (x <= 14.0 + 0.5 * keel::abs(nu)) {
        const keel::f64 halfX = 0.5 * x;
        const keel::f64 halfX2 = halfX * halfX;
        keel::f64 sum = 0.0;
        if (nu >= 0.0) {
            keel::f64 term = keel::exp(nu * keel::log(halfX) - keel::lgamma(nu + 1.0));
            sum = term;
            for (keel::i32 k = 1; k <= 160; ++k) {
                term *= halfX2 / (keel::as<keel::f64>(k) * (nu + keel::as<keel::f64>(k)));
                sum += term;
                if (keel::abs(term) <= keel::abs(sum) * 1e-16 && k > halfX)
                    break;
            }
        } else {
            for (keel::i32 k = 0; k <= 160; ++k) {
                const keel::f64 gArg = nu + keel::as<keel::f64>(k) + 1.0;
                const keel::f64 gam = keel::tgamma(gArg);
                if (!keel::is_finite(gam) || gam == 0.0)
                    continue;
                const keel::f64 kFact = keel::tgamma(keel::as<keel::f64>(k) + 1.0);
                const keel::f64 term = keel::pow(halfX, 2.0 * k + nu) / (kFact * gam);
                sum += term;
                if (k > 10 && keel::abs(term) <= keel::abs(sum) * 1e-16 && k > halfX)
                    break;
            }
        }
        out = signFactor * sum;
        return keel::is_finite(out);
    }
    const keel::f64 mu = 4.0 * nu * nu;
    keel::f64 sum = 1.0, term = 1.0;
    for (keel::i32 k = 1; k <= 24; ++k) {
        const keel::f64 num = mu - keel::as<keel::f64>((2 * k - 1) * (2 * k - 1));
        const keel::f64 next = -term * num / (keel::as<keel::f64>(k) * 8.0 * x);
        if (k > 4 && keel::abs(next) > keel::abs(term))
            break;
        term = next;
        sum += term;
        if (keel::abs(term) < 1e-16)
            break;
    }
    out = signFactor * (keel::exp(x) / keel::sqrt(2.0 * kPiDouble * x)) * sum;
    return keel::is_finite(out);
}

bool evalBesselKDouble(keel::f64 nu, keel::f64 x, keel::f64 &out)
{
    if (!keel::is_finite(nu) || !keel::is_finite(x) || x <= 0.0)
        return false;
    nu = keel::abs(nu);
    if (x > 9.0 + 0.5 * nu) {
        const keel::f64 mu = 4.0 * nu * nu;
        keel::f64 sum = 1.0, term = 1.0;
        for (keel::i32 k = 1; k <= 24; ++k) {
            const keel::f64 num = mu - keel::as<keel::f64>((2 * k - 1) * (2 * k - 1));
            const keel::f64 next = term * num / (keel::as<keel::f64>(k) * 8.0 * x);
            if (k > 4 && keel::abs(next) > keel::abs(term))
                break;
            term = next;
            sum += term;
            if (keel::abs(term) < 1e-16)
                break;
        }
        out = keel::sqrt(kPiDouble / (2.0 * x)) * keel::exp(-x) * sum;
        return keel::is_finite(out);
    }
    if (keel::floor(nu) != nu) {
        keel::f64 iPos = 0.0, iNeg = 0.0;
        if (!evalBesselIDouble(nu, x, iPos) || !evalBesselIDouble(-nu, x, iNeg))
            return false;
        out = (0.5 * kPiDouble) * (iNeg - iPos) / keel::sin(nu * kPiDouble);
        return keel::is_finite(out);
    }
    const keel::i32 n = keel::as<keel::i32>(nu);
    if (n > 30)
        return false;
    keel::f64 inVal = 0.0;
    if (!evalBesselIDouble(keel::as<keel::f64>(n), x, inVal))
        return false;
    const keel::f64 halfX = 0.5 * x;
    const keel::f64 halfX2 = halfX * halfX;
    keel::f64 poleSum = 0.0;
    for (keel::i32 k = 0; k < n; ++k) {
        const keel::f64 sgn = (k % 2 == 0) ? 1.0 : -1.0;
        const keel::f64 numFact = keel::tgamma(keel::as<keel::f64>(n - k));
        const keel::f64 denFact = keel::tgamma(keel::as<keel::f64>(k + 1));
        poleSum += sgn * (numFact / denFact) * keel::pow(halfX, 2 * k - n);
    }
    keel::f64 hN = 0.0;
    for (keel::i32 j = 1; j <= n; ++j)
        hN += 1.0 / keel::as<keel::f64>(j);
    keel::f64 hK = 0.0;
    keel::f64 powTerm = keel::pow(halfX, n) / keel::tgamma(keel::as<keel::f64>(n + 1));
    keel::f64 regSum = (hK + hN) * powTerm;
    for (keel::i32 k = 1; k <= 120; ++k) {
        hK += 1.0 / keel::as<keel::f64>(k);
        hN += 1.0 / keel::as<keel::f64>(n + k);
        powTerm *= halfX2 / (keel::as<keel::f64>(k) * keel::as<keel::f64>(n + k));
        const keel::f64 contrib = (hK + hN) * powTerm;
        regSum += contrib;
        if (keel::abs(contrib) <= keel::abs(regSum) * 1e-16 && k > halfX)
            break;
    }
    const keel::f64 sgnN = (n % 2 == 0) ? 1.0 : -1.0;
    out = -sgnN * (keel::log(halfX) + kEulerGamma) * inVal + 0.5 * poleSum +
          0.5 * sgnN * regSum;
    return keel::is_finite(out);
}

bool evalAiryDouble(keel::StringRef fn, keel::f64 x, keel::f64 &out)
{
    if (!keel::is_finite(x))
        return false;
    static constexpr keel::f64 kAi0 = 0.35502805388781723926;
    static constexpr keel::f64 kAiP0 = 0.25881940379280679840;
    const keel::f64 sqrt3 = keel::sqrt(3.0);
    if (keel::abs(x) <= 5.5) {
        const keel::f64 x2 = x * x;
        const keel::f64 x3 = x2 * x;
        keel::f64 f = 1.0, fp = 0.0, cTerm = 1.0;
        keel::f64 g = x, gp = 1.0, dTerm = 1.0;
        for (keel::i32 k = 1; k <= 60; ++k) {
            cTerm *= x3 / keel::as<keel::f64>((3 * k - 1) * (3 * k));
            f += cTerm;
            fp += keel::as<keel::f64>(3 * k) * (cTerm / x);
            dTerm *= x3 / keel::as<keel::f64>((3 * k) * (3 * k + 1));
            g += dTerm * x;
            gp += keel::as<keel::f64>(3 * k + 1) * dTerm;
            if (keel::abs(cTerm) <= 1e-16 && keel::abs(dTerm) <= 1e-16)
                break;
        }
        if (x == 0.0) {
            fp = 0.0;
            gp = 1.0;
        }
        if (fn == "airyAi")
            out = kAi0 * f - kAiP0 * g;
        else if (fn == "airyBi")
            out = sqrt3 * (kAi0 * f + kAiP0 * g);
        else if (fn == "airyAiPrime")
            out = kAi0 * fp - kAiP0 * gp;
        else if (fn == "airyBiPrime")
            out = sqrt3 * (kAi0 * fp + kAiP0 * gp);
        else
            return false;
        return keel::is_finite(out);
    }
    const keel::f64 ax = keel::abs(x);
    const keel::f64 zeta = (2.0 / 3.0) * ax * keel::sqrt(ax);
    if (x > 0.0) {
        if (fn == "airyAi") {
            keel::f64 kVal = 0.0;
            if (!evalBesselKDouble(1.0 / 3.0, zeta, kVal))
                return false;
            out = (1.0 / kPiDouble) * keel::sqrt(x / 3.0) * kVal;
            return keel::is_finite(out);
        }
        if (fn == "airyAiPrime") {
            keel::f64 kVal = 0.0;
            if (!evalBesselKDouble(2.0 / 3.0, zeta, kVal))
                return false;
            out = -(x / (kPiDouble * sqrt3)) * kVal;
            return keel::is_finite(out);
        }
        if (fn == "airyBi") {
            keel::f64 iPos = 0.0, iNeg = 0.0;
            if (!evalBesselIDouble(1.0 / 3.0, zeta, iPos) ||
                !evalBesselIDouble(-1.0 / 3.0, zeta, iNeg))
                return false;
            out = keel::sqrt(x / 3.0) * (iNeg + iPos);
            return keel::is_finite(out);
        }
        if (fn == "airyBiPrime") {
            keel::f64 iPos = 0.0, iNeg = 0.0;
            if (!evalBesselIDouble(2.0 / 3.0, zeta, iPos) ||
                !evalBesselIDouble(-2.0 / 3.0, zeta, iNeg))
                return false;
            out = (x / sqrt3) * (iNeg + iPos);
            return keel::is_finite(out);
        }
        return false;
    }
    // x < -5.5
    keel::f64 j13 = 0.0, jm13 = 0.0, j23 = 0.0, jm23 = 0.0;
    if (fn == "airyAi" || fn == "airyBi") {
        if (!evalBesselJDouble(1.0 / 3.0, zeta, j13) ||
            !evalBesselJDouble(-1.0 / 3.0, zeta, jm13))
            return false;
        out = (fn == "airyAi") ? (keel::sqrt(ax) / 3.0) * (j13 + jm13)
                               : keel::sqrt(ax / 3.0) * (jm13 - j13);
        return keel::is_finite(out);
    }
    if (fn == "airyAiPrime" || fn == "airyBiPrime") {
        if (!evalBesselJDouble(2.0 / 3.0, zeta, j23) ||
            !evalBesselJDouble(-2.0 / 3.0, zeta, jm23))
            return false;
        out = (fn == "airyAiPrime") ? -(ax / 3.0) * (j23 - jm23)
                                    : (ax / sqrt3) * (j23 + jm23);
        return keel::is_finite(out);
    }
    return false;
}

bool evalOrthogonalPolyDouble(keel::StringRef fn, keel::f64 nVal, keel::f64 x,
                              keel::f64 &out)
{
    if (!keel::is_finite(nVal) || !keel::is_finite(x) || keel::floor(nVal) != nVal)
        return false;
    keel::i32 n = keel::as<keel::i32>(nVal);
    if (fn == "legendreP") {
        if (n < 0) n = -n - 1;
        if (n > 200) return false;
        if (n == 0) { out = 1.0; return true; }
        if (n == 1) { out = x; return true; }
        keel::f64 pPrev = 1.0, pCur = x;
        for (keel::i32 k = 1; k < n; ++k) {
            const keel::f64 pNext =
                ((2.0 * k + 1.0) * x * pCur - k * pPrev) / (k + 1.0);
            pPrev = pCur;
            pCur = pNext;
        }
        out = pCur;
        return keel::is_finite(out);
    }
    if (fn == "chebyshevT") {
        if (n < 0) n = -n;
        if (n > 200) return false;
        if (n == 0) { out = 1.0; return true; }
        if (n == 1) { out = x; return true; }
        keel::f64 tPrev = 1.0, tCur = x;
        for (keel::i32 k = 1; k < n; ++k) {
            const keel::f64 tNext = 2.0 * x * tCur - tPrev;
            tPrev = tCur;
            tCur = tNext;
        }
        out = tCur;
        return keel::is_finite(out);
    }
    if (fn == "chebyshevU") {
        keel::f64 sgn = 1.0;
        if (n == -1) { out = 0.0; return true; }
        if (n < -1) { n = -n - 2; sgn = -1.0; }
        if (n > 200) return false;
        if (n == 0) { out = sgn; return true; }
        if (n == 1) { out = sgn * 2.0 * x; return true; }
        keel::f64 uPrev = 1.0, uCur = 2.0 * x;
        for (keel::i32 k = 1; k < n; ++k) {
            const keel::f64 uNext = 2.0 * x * uCur - uPrev;
            uPrev = uCur;
            uCur = uNext;
        }
        out = sgn * uCur;
        return keel::is_finite(out);
    }
    if (fn == "hermiteH") {
        if (n < 0 || n > 200) return false;
        if (n == 0) { out = 1.0; return true; }
        if (n == 1) { out = 2.0 * x; return true; }
        keel::f64 hPrev = 1.0, hCur = 2.0 * x;
        for (keel::i32 k = 1; k < n; ++k) {
            const keel::f64 hNext = 2.0 * x * hCur - 2.0 * k * hPrev;
            hPrev = hCur;
            hCur = hNext;
        }
        out = hCur;
        return keel::is_finite(out);
    }
    if (fn == "laguerreL") {
        if (n < 0 || n > 200) return false;
        if (n == 0) { out = 1.0; return true; }
        if (n == 1) { out = 1.0 - x; return true; }
        keel::f64 lPrev = 1.0, lCur = 1.0 - x;
        for (keel::i32 k = 1; k < n; ++k) {
            const keel::f64 lNext =
                ((2.0 * k + 1.0 - x) * lCur - k * lPrev) / (k + 1.0);
            lPrev = lCur;
            lCur = lNext;
        }
        out = lCur;
        return keel::is_finite(out);
    }
    return false;
}

bool carlsonRF(keel::f64 x, keel::f64 y, keel::f64 z, keel::f64 &out)
{
    if (!keel::is_finite(x) || !keel::is_finite(y) || !keel::is_finite(z) ||
        x < 0.0 || y < 0.0 || z < 0.0)
        return false;
    keel::i32 zeroCount = (x == 0.0 ? 1 : 0) + (y == 0.0 ? 1 : 0) + (z == 0.0 ? 1 : 0);
    if (zeroCount > 1)
        return false;

    for (keel::i32 iter = 0; iter < 36; ++iter) {
        const keel::f64 A = (x + y + z) / 3.0;
        const keel::f64 dx = keel::abs(A - x);
        const keel::f64 dy = keel::abs(A - y);
        const keel::f64 dz = keel::abs(A - z);
        if (keel::max({dx, dy, dz}) <= 1e-6 * A)
            break;
        const keel::f64 sx = keel::sqrt(x);
        const keel::f64 sy = keel::sqrt(y);
        const keel::f64 sz = keel::sqrt(z);
        const keel::f64 lam = sx * sy + sy * sz + sz * sx;
        x = 0.25 * (x + lam);
        y = 0.25 * (y + lam);
        z = 0.25 * (z + lam);
    }
    const keel::f64 A = (x + y + z) / 3.0;
    if (A <= 0.0)
        return false;
    const keel::f64 X = (A - x) / A;
    const keel::f64 Y = (A - y) / A;
    const keel::f64 Z = -X - Y;
    const keel::f64 E2 = X * Y - Z * Z;
    const keel::f64 E3 = X * Y * Z;
    out = (1.0 - (1.0 / 10.0) * E2 + (1.0 / 14.0) * E3 +
           (1.0 / 24.0) * E2 * E2 - (3.0 / 44.0) * E2 * E3) /
          keel::sqrt(A);
    return keel::is_finite(out);
}

bool carlsonRD(keel::f64 x, keel::f64 y, keel::f64 z, keel::f64 &out)
{
    if (!keel::is_finite(x) || !keel::is_finite(y) || !keel::is_finite(z) ||
        x < 0.0 || y < 0.0 || z <= 0.0 || (x + y <= 0.0))
        return false;

    keel::f64 sum = 0.0;
    keel::f64 fac = 1.0;
    for (keel::i32 iter = 0; iter < 36; ++iter) {
        const keel::f64 A = (x + y + 3.0 * z) / 5.0;
        const keel::f64 dx = keel::abs(A - x);
        const keel::f64 dy = keel::abs(A - y);
        const keel::f64 dz = keel::abs(A - z);
        if (keel::max({dx, dy, dz}) <= 1e-6 * A)
            break;
        const keel::f64 sx = keel::sqrt(x);
        const keel::f64 sy = keel::sqrt(y);
        const keel::f64 sz = keel::sqrt(z);
        const keel::f64 lam = sx * sy + sy * sz + sz * sx;
        sum += fac / (sz * (z + lam));
        fac *= 0.25;
        x = 0.25 * (x + lam);
        y = 0.25 * (y + lam);
        z = 0.25 * (z + lam);
    }
    const keel::f64 A = (x + y + 3.0 * z) / 5.0;
    if (A <= 0.0)
        return false;
    const keel::f64 X = (A - x) / A;
    const keel::f64 Y = (A - y) / A;
    const keel::f64 Z = -(X + Y) / 3.0;
    const keel::f64 E2 = X * Y - 6.0 * Z * Z;
    const keel::f64 E3 = (3.0 * X * Y - 8.0 * Z * Z) * Z;
    const keel::f64 E4 = 3.0 * (X * Y - Z * Z) * Z * Z;
    const keel::f64 E5 = X * Y * Z * Z * Z;
    const keel::f64 poly =
        1.0 - (3.0 / 14.0) * E2 + (1.0 / 6.0) * E3 +
        (9.0 / 88.0) * E2 * E2 - (3.0 / 22.0) * E4 -
        (9.0 / 52.0) * E2 * E3 + (3.0 / 26.0) * E5;
    out = 3.0 * sum + fac * poly / (A * keel::sqrt(A));
    return keel::is_finite(out);
}

bool carlsonRJ(keel::f64 x, keel::f64 y, keel::f64 z, keel::f64 p, keel::f64 &out)
{
    if (!keel::is_finite(x) || !keel::is_finite(y) || !keel::is_finite(z) ||
        !keel::is_finite(p) || x < 0.0 || y < 0.0 || z < 0.0 || p <= 0.0)
        return false;
    keel::i32 zeroCount = (x == 0.0 ? 1 : 0) + (y == 0.0 ? 1 : 0) + (z == 0.0 ? 1 : 0);
    if (zeroCount > 1)
        return false;

    keel::f64 sum = 0.0;
    keel::f64 fac = 1.0;
    for (keel::i32 iter = 0; iter < 36; ++iter) {
        const keel::f64 A = (x + y + z + 2.0 * p) / 5.0;
        const keel::f64 dx = keel::abs(A - x);
        const keel::f64 dy = keel::abs(A - y);
        const keel::f64 dz = keel::abs(A - z);
        const keel::f64 dp = keel::abs(A - p);
        if (keel::max({dx, dy, dz, dp}) <= 1e-6 * A)
            break;
        const keel::f64 sx = keel::sqrt(x);
        const keel::f64 sy = keel::sqrt(y);
        const keel::f64 sz = keel::sqrt(z);
        const keel::f64 sp = keel::sqrt(p);
        const keel::f64 lam = sx * sy + sy * sz + sz * sx;
        const keel::f64 d = (sp + sx) * (sp + sy) * (sp + sz);
        if (d == 0.0)
            return false;
        const keel::f64 e = ((p - x) * (p - y) * (p - z)) / (d * d);
        if (e <= -1.0)
            return false;
        keel::f64 rc = 1.0;
        if (keel::abs(e) <= 1e-8) {
            rc = 1.0 - (1.0 / 3.0) * e + (1.0 / 5.0) * e * e -
                 (1.0 / 7.0) * e * e * e;
        } else if (e > 0.0) {
            const keel::f64 se = keel::sqrt(e);
            rc = keel::atan(se) / se;
        } else {
            const keel::f64 sme = keel::sqrt(-e);
            rc = keel::atanh(sme) / sme;
        }
        sum += fac * rc / d;
        fac *= 0.25;
        x = 0.25 * (x + lam);
        y = 0.25 * (y + lam);
        z = 0.25 * (z + lam);
        p = 0.25 * (p + lam);
    }
    const keel::f64 A = (x + y + z + 2.0 * p) / 5.0;
    if (A <= 0.0)
        return false;
    const keel::f64 X = (A - x) / A;
    const keel::f64 Y = (A - y) / A;
    const keel::f64 Z = (A - z) / A;
    const keel::f64 P = -(X + Y + Z) / 2.0;
    const keel::f64 E2 = X * Y + X * Z + Y * Z - 3.0 * P * P;
    const keel::f64 E3 = X * Y * Z + 2.0 * E2 * P + 4.0 * P * P * P;
    const keel::f64 E4 = (2.0 * X * Y * Z + E2 * P + 3.0 * P * P * P) * P;
    const keel::f64 E5 = X * Y * Z * P * P;
    const keel::f64 poly =
        1.0 - (3.0 / 14.0) * E2 + (1.0 / 6.0) * E3 +
        (9.0 / 88.0) * E2 * E2 - (3.0 / 22.0) * E4 -
        (9.0 / 52.0) * E2 * E3 + (3.0 / 26.0) * E5;
    out = 6.0 * sum + fac * poly / (A * keel::sqrt(A));
    return keel::is_finite(out);
}

bool evalElliptic1ArgDouble(keel::StringRef fn, keel::f64 m, keel::f64 &out)
{
    if (!keel::is_finite(m) || m > 1.0)
        return false;
    if (fn == "ellipticK") {
        if (m >= 1.0)
            return false;
        return carlsonRF(0.0, 1.0 - m, 1.0, out);
    }
    if (fn == "ellipticE") {
        if (m == 1.0) {
            out = 1.0;
            return true;
        }
        keel::f64 rf = 0.0, rd = 0.0;
        if (!carlsonRF(0.0, 1.0 - m, 1.0, rf) ||
            !carlsonRD(0.0, 1.0 - m, 1.0, rd))
            return false;
        out = rf - (m / 3.0) * rd;
        return keel::is_finite(out);
    }
    return false;
}

bool evalElliptic2ArgDouble(keel::StringRef fn, keel::f64 a0, keel::f64 a1,
                            keel::f64 &out)
{
    if (!keel::is_finite(a0) || !keel::is_finite(a1))
        return false;
    if (fn == "ellipticPi") {
        const keel::f64 n = a0;
        const keel::f64 m = a1;
        if (m >= 1.0 || n >= 1.0)
            return false;
        keel::f64 rf = 0.0;
        if (!carlsonRF(0.0, 1.0 - m, 1.0, rf))
            return false;
        if (n == 0.0) {
            out = rf;
            return true;
        }
        keel::f64 rj = 0.0;
        if (!carlsonRJ(0.0, 1.0 - m, 1.0, 1.0 - n, rj))
            return false;
        out = rf + (n / 3.0) * rj;
        return keel::is_finite(out);
    }
    if (fn == "ellipticF" || fn == "ellipticEInc" || fn == "ellipticE") {
        const keel::f64 phi = a0;
        const keel::f64 m = a1;
        if (phi == 0.0) {
            out = 0.0;
            return true;
        }
        const keel::f64 k = keel::floor(phi / kPiDouble + 0.5);
        const keel::f64 phi0 = phi - k * kPiDouble;
        const keel::f64 s = keel::sin(phi0);
        const keel::f64 c = keel::cos(phi0);
        const keel::f64 s2 = s * s;
        const keel::f64 c2 = c * c;
        if (1.0 - m * s2 < 0.0)
            return false;
        keel::f64 baseVal = 0.0;
        if (s == 0.0) {
            baseVal = 0.0;
        } else if (fn == "ellipticF") {
            if (1.0 - m * s2 == 0.0 && c2 == 0.0)
                return false;
            keel::f64 rf = 0.0;
            if (!carlsonRF(c2, 1.0 - m * s2, 1.0, rf))
                return false;
            baseVal = s * rf;
        } else {
            keel::f64 rf = 0.0;
            if (!carlsonRF(c2, 1.0 - m * s2, 1.0, rf))
                return false;
            keel::f64 rdTerm = 0.0;
            if (m != 0.0) {
                keel::f64 rd = 0.0;
                if (!carlsonRD(c2, 1.0 - m * s2, 1.0, rd))
                    return false;
                rdTerm = (m / 3.0) * s * s2 * rd;
            }
            baseVal = s * rf - rdTerm;
        }
        if (k != 0.0) {
            keel::f64 compVal = 0.0;
            const keel::StringRef compFn =
                (fn == "ellipticF") ? "ellipticK" : "ellipticE";
            if (!evalElliptic1ArgDouble(compFn, m, compVal))
                return false;
            out = 2.0 * k * compVal + baseVal;
        } else {
            out = baseVal;
        }
        return keel::is_finite(out);
    }
    return false;
}

bool evalZetaDouble(keel::f64 s, keel::f64 &out)
{
    if (!keel::is_finite(s) || s == 1.0)
        return false;
    if (s == 0.0) {
        out = -0.5;
        return true;
    }
    if (s < 0.0 && keel::floor(s) == s) {
        const keel::i64 m = keel::as<keel::i64>(-s);
        if (m % 2 == 0) {
            out = 0.0;
            return true;
        }
    }
    if (s < 0.5) {
        keel::f64 zComp = 0.0;
        if (!evalZetaDouble(1.0 - s, zComp))
            return false;
        out = keel::pow(2.0, s) * keel::pow(kPiDouble, s - 1.0) *
              keel::sin(0.5 * kPiDouble * s) * keel::tgamma(1.0 - s) * zComp;
        return keel::is_finite(out);
    }
    // Euler-Maclaurin summation with N = 16 and 8 Bernoulli correction terms.
    static constexpr keel::f64 kB2kOverFact[8] = {
        (1.0 / 6.0) / 2.0,
        (-1.0 / 30.0) / 24.0,
        (1.0 / 42.0) / 720.0,
        (-1.0 / 30.0) / 40320.0,
        (5.0 / 66.0) / 3628800.0,
        (-691.0 / 2730.0) / 479001600.0,
        (7.0 / 6.0) / 87178291200.0,
        (-3617.0 / 510.0) / 20922789888000.0};
    constexpr keel::i32 N = 16;
    keel::f64 sum = 0.0;
    for (keel::i32 n = 1; n < N; ++n)
        sum += keel::pow(keel::as<keel::f64>(n), -s);
    const keel::f64 nD = keel::as<keel::f64>(N);
    const keel::f64 nPowNegS = keel::pow(nD, -s);
    sum += (nD * nPowNegS) / (s - 1.0) + 0.5 * nPowNegS;

    const keel::f64 invN2 = 1.0 / (nD * nD);
    keel::f64 poch = s;
    keel::f64 nFactor = nPowNegS / nD;
    for (keel::i32 k = 1; k <= 8; ++k) {
        if (k > 1) {
            poch *= (s + keel::as<keel::f64>(2 * k - 3)) *
                    (s + keel::as<keel::f64>(2 * k - 2));
            nFactor *= invN2;
        }
        const keel::f64 contrib = kB2kOverFact[k - 1] * poch * nFactor;
        sum += contrib;
        if (keel::abs(contrib) <= 1e-16 * keel::abs(sum))
            break;
    }
    out = sum;
    return keel::is_finite(out);
}

bool evalDirichletEtaDouble(keel::f64 s, keel::f64 &out)
{
    if (!keel::is_finite(s))
        return false;
    if (s == 1.0) {
        out = keel::log(2.0);
        return true;
    }
    keel::f64 z = 0.0;
    if (!evalZetaDouble(s, z))
        return false;
    out = (1.0 - keel::pow(2.0, 1.0 - s)) * z;
    return keel::is_finite(out);
}

bool evalPolylogDouble(keel::f64 s, keel::f64 z, keel::f64 &out)
{
    if (!keel::is_finite(s) || !keel::is_finite(z) || z > 1.0)
        return false;
    if (z == 0.0) {
        out = 0.0;
        return true;
    }
    if (s == 2.0)
        return evalDilogDouble(z, out);
    if (s == 1.0) {
        if (z >= 1.0)
            return false;
        out = -keel::log(1.0 - z);
        return keel::is_finite(out);
    }
    if (z == 1.0) {
        if (s <= 1.0)
            return false;
        return evalZetaDouble(s, out);
    }
    if (z == -1.0) {
        keel::f64 eta = 0.0;
        if (!evalDirichletEtaDouble(s, eta))
            return false;
        out = -eta;
        return keel::is_finite(out);
    }
    if (s <= 0.0 && keel::floor(s) == s) {
        const keel::i64 m = keel::as<keel::i64>(-s);
        if (m == 0) {
            out = z / (1.0 - z);
            return keel::is_finite(out);
        }
        if (m <= 20) {
            keel::Array<keel::f64> eul(m, 0.0);
            eul[0] = 1.0;
            for (keel::i64 i = 2; i <= m; ++i) {
                for (keel::i64 k = i - 1; k >= 1; --k) {
                    eul[keel::as<keel::usize>(k)] =
                        keel::as<keel::f64>(k + 1) *
                            eul[keel::as<keel::usize>(k)] +
                        keel::as<keel::f64>(i - k) *
                            eul[keel::as<keel::usize>(k - 1)];
                }
            }
            keel::f64 num = 0.0;
            for (keel::i64 k = 0; k < m; ++k) {
                num += eul[keel::as<keel::usize>(k)] *
                       keel::pow(z, keel::as<keel::f64>(m - k));
            }
            out = num / keel::pow(1.0 - z, keel::as<keel::f64>(m + 1));
            return keel::is_finite(out);
        }
    }
    if (keel::abs(z) <= 0.75) {
        keel::f64 sum = 0.0;
        keel::f64 zPow = z;
        for (keel::i32 k = 1; k <= 160; ++k) {
            const keel::f64 contrib = zPow * keel::pow(keel::as<keel::f64>(k), -s);
            sum += contrib;
            if (keel::abs(contrib) <= 1e-16 * keel::abs(sum))
                break;
            zPow *= z;
        }
        out = sum;
        return keel::is_finite(out);
    }
    if (z < 1.0 && z > -1.0) {
        keel::f64 sum = 0.0;
        keel::f64 zPow = z;
        for (keel::i32 k = 1; k <= 800; ++k) {
            const keel::f64 contrib = zPow * keel::pow(keel::as<keel::f64>(k), -s);
            sum += contrib;
            if (keel::abs(contrib) <= 1e-16 * keel::abs(sum))
                break;
            zPow *= z;
        }
        out = sum;
        return keel::is_finite(out);
    }
    return false;
}

bool evalBernoulliEuler2ArgDouble(keel::StringRef fn, keel::f64 nVal, keel::f64 x,
                                  keel::f64 &out)
{
    if (!keel::is_finite(nVal) || !keel::is_finite(x) || keel::floor(nVal) != nVal)
        return false;
    const keel::i64 n = keel::as<keel::i64>(nVal);
    if (n < 0 || n > 40)
        return false;
    if (fn == "bernoulliB") {
        keel::f64 sum = 0.0;
        keel::f64 binom = 1.0;
        for (keel::i64 k = 0; k <= n; ++k) {
            if (k > 0)
                binom = (binom * keel::as<keel::f64>(n - k + 1)) /
                        keel::as<keel::f64>(k);
            Rational bk;
            if (!bernoulliExact(k, bk))
                return false;
            if (!bk.isZero()) {
                sum += binom * bk.toDouble() *
                       keel::pow(x, keel::as<keel::f64>(n - k));
            }
        }
        out = sum;
        return keel::is_finite(out);
    }
    if (fn == "eulerE") {
        const keel::f64 xShift = x - 0.5;
        keel::f64 sum = 0.0;
        keel::f64 binom = 1.0;
        for (keel::i64 k = 0; k <= n; ++k) {
            if (k > 0)
                binom = (binom * keel::as<keel::f64>(n - k + 1)) /
                        keel::as<keel::f64>(k);
            Rational ek;
            if (!eulerExact(k, ek))
                return false;
            if (!ek.isZero()) {
                sum += binom * ek.toDouble() *
                       keel::pow(2.0, -keel::as<keel::f64>(k)) *
                       keel::pow(xShift, keel::as<keel::f64>(n - k));
            }
        }
        out = sum;
        return keel::is_finite(out);
    }
    return false;
}

bool evalBetaDouble(keel::f64 x, keel::f64 y, keel::f64 &out)
{
    if (!keel::is_finite(x) || !keel::is_finite(y))
        return false;
    const keel::f64 xy = x + y;
    if ((x <= 0.0 && keel::floor(x) == x) || (y <= 0.0 && keel::floor(y) == y))
        return false;
    if (xy <= 0.0 && keel::floor(xy) == xy) {
        out = 0.0;
        return true;
    }
    if (x > 0.0 && y > 0.0) {
        out = keel::exp(keel::lgamma(x) + keel::lgamma(y) - keel::lgamma(xy));
        return keel::is_finite(out);
    }
    const keel::f64 gx = keel::tgamma(x);
    const keel::f64 gy = keel::tgamma(y);
    const keel::f64 gxy = keel::tgamma(xy);
    if (!keel::is_finite(gx) || !keel::is_finite(gy) || !keel::is_finite(gxy) ||
        gxy == 0.0)
        return false;
    out = (gx * gy) / gxy;
    return keel::is_finite(out);
}

bool evalPochhammerDouble(keel::f64 a, keel::f64 n, keel::f64 &out)
{
    if (!keel::is_finite(a) || !keel::is_finite(n))
        return false;
    if (keel::floor(n) == n && n >= 0.0 && n <= 60.0) {
        const keel::i32 k = keel::as<keel::i32>(n);
        keel::f64 prod = 1.0;
        for (keel::i32 j = 0; j < k; ++j)
            prod *= (a + keel::as<keel::f64>(j));
        out = prod;
        return keel::is_finite(out);
    }
    const keel::f64 an = a + n;
    if ((a <= 0.0 && keel::floor(a) == a) || (an <= 0.0 && keel::floor(an) == an))
        return false;
    if (a > 0.0 && an > 0.0) {
        out = keel::exp(keel::lgamma(an) - keel::lgamma(a));
        return keel::is_finite(out);
    }
    out = keel::tgamma(an) / keel::tgamma(a);
    return keel::is_finite(out);
}

bool evalIncompleteGammaDouble(keel::StringRef fn, keel::f64 s, keel::f64 x,
                               keel::f64 &out)
{
    if (!keel::is_finite(s) || !keel::is_finite(x) || x < 0.0 || s <= 0.0)
        return false;
    if (x == 0.0) {
        out = (fn == "gammainc") ? 0.0 : keel::tgamma(s);
        return keel::is_finite(out);
    }
    const keel::f64 gs = keel::tgamma(s);
    if (!keel::is_finite(gs))
        return false;
    keel::f64 lower = 0.0, upper = 0.0;
    if (x < s + 1.0) {
        keel::f64 sum = 1.0 / s;
        keel::f64 term = sum;
        for (keel::i32 k = 1; k <= 300; ++k) {
            term *= x / (s + keel::as<keel::f64>(k));
            sum += term;
            if (keel::abs(term) <= 1e-16 * keel::abs(sum))
                break;
        }
        lower = keel::pow(x, s) * keel::exp(-x) * sum;
        upper = gs - lower;
    } else {
        // Legendre continued fraction for upper incomplete gamma via Lentz's method.
        constexpr keel::f64 tiny = 1e-30;
        keel::f64 b = x + 1.0 - s;
        keel::f64 c = 1.0 / tiny;
        keel::f64 d = 1.0 / b;
        keel::f64 h = d;
        for (keel::i32 i = 1; i <= 300; ++i) {
            const keel::f64 an = -keel::as<keel::f64>(i) * (keel::as<keel::f64>(i) - s);
            b += 2.0;
            d = an * d + b;
            if (keel::abs(d) < tiny)
                d = tiny;
            c = b + an / c;
            if (keel::abs(c) < tiny)
                c = tiny;
            d = 1.0 / d;
            const keel::f64 del = d * c;
            h *= del;
            if (keel::abs(del - 1.0) <= 1e-16)
                break;
        }
        upper = keel::pow(x, s) * keel::exp(-x) * h;
        lower = gs - upper;
    }
    out = (fn == "gammainc") ? lower : upper;
    return keel::is_finite(out);
}

bool evalHypergeom0F1Double(keel::f64 b, keel::f64 z, keel::f64 &out)
{
    if (!keel::is_finite(b) || !keel::is_finite(z))
        return false;
    if (b <= 0.0 && keel::floor(b) == b)
        return false;
    keel::f64 sum = 1.0, term = 1.0;
    for (keel::i32 k = 1; k <= 300; ++k) {
        const keel::f64 den = (b + keel::as<keel::f64>(k - 1)) * keel::as<keel::f64>(k);
        if (den == 0.0)
            return false;
        term *= z / den;
        sum += term;
        if (keel::abs(term) <= 1e-16 * keel::abs(sum) && k > keel::abs(z))
            break;
    }
    out = sum;
    return keel::is_finite(out);
}

bool evalHypergeom1F1Double(keel::f64 a, keel::f64 b, keel::f64 z, keel::f64 &out)
{
    if (!keel::is_finite(a) || !keel::is_finite(b) || !keel::is_finite(z))
        return false;
    if (z == 0.0 || a == 0.0) {
        out = 1.0;
        return true;
    }
    const bool aNegInt = (a <= 0.0 && keel::floor(a) == a);
    if (b <= 0.0 && keel::floor(b) == b) {
        if (!aNegInt || b < a)
            return false;
    }
    if (!aNegInt && z < -15.0) {
        // Kummer's 1st transformation: 1F1(a, b, z) = exp(z) * 1F1(b - a, b, -z)
        keel::f64 kVal = 0.0;
        if (!evalHypergeom1F1Double(b - a, b, -z, kVal))
            return false;
        out = keel::exp(z) * kVal;
        return keel::is_finite(out);
    }
    const keel::i32 maxSteps = aNegInt ? keel::as<keel::i32>(-a) : 400;
    keel::f64 sum = 1.0, term = 1.0;
    for (keel::i32 k = 1; k <= maxSteps; ++k) {
        const keel::f64 num = a + keel::as<keel::f64>(k - 1);
        const keel::f64 den = (b + keel::as<keel::f64>(k - 1)) * keel::as<keel::f64>(k);
        if (den == 0.0)
            return false;
        term *= (num * z) / den;
        sum += term;
        if (!aNegInt && keel::abs(term) <= 1e-16 * keel::abs(sum) &&
            k > keel::abs(z))
            break;
    }
    out = sum;
    return keel::is_finite(out);
}

bool evalHypergeom2F1Double(keel::f64 a, keel::f64 b, keel::f64 c, keel::f64 z, keel::f64 &out)
{
    if (!keel::is_finite(a) || !keel::is_finite(b) || !keel::is_finite(c) ||
        !keel::is_finite(z))
        return false;
    if (z == 0.0 || a == 0.0 || b == 0.0) {
        out = 1.0;
        return true;
    }
    const bool aNegInt = (a <= 0.0 && keel::floor(a) == a && a >= -200.0);
    const bool bNegInt = (b <= 0.0 && keel::floor(b) == b && b >= -200.0);
    const bool terminates = aNegInt || bNegInt;
    keel::i32 termCount = 500;
    if (aNegInt && bNegInt)
        termCount = keel::as<keel::i32>(keel::min(-a, -b));
    else if (aNegInt)
        termCount = keel::as<keel::i32>(-a);
    else if (bNegInt)
        termCount = keel::as<keel::i32>(-b);

    if (!terminates) {
        if (c <= 0.0 && keel::floor(c) == c)
            return false;
        if (z > 1.0)
            return false;
        if (z == 1.0) {
            const keel::f64 cab = c - a - b;
            if (cab <= 0.0)
                return false;
            out = (keel::tgamma(c) * keel::tgamma(cab)) /
                  (keel::tgamma(c - a) * keel::tgamma(c - b));
            return keel::is_finite(out);
        }
        if (z < -0.5) {
            // Pfaff transformation: 2F1(a, b; c; z) = (1 - z)^(-a) * 2F1(a, c - b; c; z / (z - 1))
            const keel::f64 w = z / (z - 1.0);
            keel::f64 pfVal = 0.0;
            if (!evalHypergeom2F1Double(a, c - b, c, w, pfVal))
                return false;
            out = keel::pow(1.0 - z, -a) * pfVal;
            return keel::is_finite(out);
        }
    }

    keel::f64 sum = 1.0, term = 1.0;
    for (keel::i32 k = 1; k <= termCount; ++k) {
        const keel::f64 num =
            (a + keel::as<keel::f64>(k - 1)) * (b + keel::as<keel::f64>(k - 1));
        const keel::f64 den =
            (c + keel::as<keel::f64>(k - 1)) * keel::as<keel::f64>(k);
        if (den == 0.0)
            return false;
        term *= (num * z) / den;
        sum += term;
        if (!terminates && keel::abs(term) <= 1e-16 * keel::abs(sum))
            break;
    }
    out = sum;
    return keel::is_finite(out);
}

bool evalDoubleRec(
    const Ctx &c, Expr e,
    keel::ArrayRef<keel::Pair<keel::StringRef, keel::f64>> vals,
    keel::HashMap<keel::u32, keel::f64> &memo, keel::f64 &out)
{
    if (e.isNull())
        return false;
    const keel::u32 nid = c.id(e);
    if (const keel::f64 *hit = memo.get(nid)) {
        out = *hit;
        return true;
    }

    keel::f64 res = 0.0;
    switch (c.kind(e)) {
    case NodeKind::Number:
        res = c.numberValue(e).toDouble();
        if (!keel::is_finite(res))
            return false;
        break;
    case NodeKind::Symbol: {
        const keel::String &name = c.symbolName(e);
        bool found = false;
        for (const auto &kv : vals) {
            if (kv.first == name) {
                res = kv.second;
                found = true;
                break;
            }
        }
        if (!found) {
            if (name.equals_ignore_ascii_case("pi")) {
                res = keel::kPi;
                found = true;
            } else if (name.equals_ignore_ascii_case("e")) {
                res = 2.718281828459045235360287471352662498;
                found = true;
            } else if (name == "euler_gamma" || name == "EulerGamma") {
                res = kEulerGamma;
                found = true;
            }
        }
        if (!found || !keel::is_finite(res))
            return false;
        break;
    }
    case NodeKind::RootOf: {
        const keel::Array<Rational> &poly = c.rootOfPoly(e);
        const keel::i32 idx = c.rootOfIndex(e);
        UPoly p = UPoly(poly.clone()).squarefreePart();
        p.makeMonic();
        const keel::Array<RootInterval> ivs = isolateRealRoots(p);
        if (idx < 0 || idx >= keel::as<keel::i32>(ivs.size()))
            return false;
        const RootInterval iv =
            refineRoot(p, ivs[keel::as<keel::usize>(idx)],
                       Rational(keel::i64{1}, BigInt(1) << 56));
        const Rational mid =
            (iv.lo + iv.hi) * Rational(keel::i64{1}, BigInt(2));
        res = mid.toDouble();
        if (!keel::is_finite(res))
            return false;
        break;
    }
    case NodeKind::Pow: {
        keel::f64 b = 0.0;
        if (!evalDoubleRec(c, c.child(e, 0), vals, memo, b))
            return false;
        const Expr expNode = c.child(e, 1);
        if (c.kind(expNode) == NodeKind::Number) {
            const Rational &er = c.numberValue(expNode);
            keel::i64 p = 0, q = 0;
            if (er.den() == BigInt(1) && er.num().fitsInt64(p)) {
                if (b == 0.0 && p <= 0)
                    return false;
                res = keel::pow(b, keel::as<keel::f64>(p));
                if (!keel::is_finite(res))
                    return false;
                break;
            }
            if (er.num().fitsInt64(p) && er.den().fitsInt64(q) && q > 0) {
                if (b < 0.0) {
                    if (q % 2 == 0)
                        return false; // even root of negative is non-real
                    const keel::f64 mag = keel::pow(-b, er.toDouble());
                    res = (p % 2 != 0) ? -mag : mag;
                    if (!keel::is_finite(res))
                        return false;
                    break;
                }
                if (b == 0.0 && p <= 0)
                    return false;
            }
        }
        keel::f64 ex = 0.0;
        if (!evalDoubleRec(c, expNode, vals, memo, ex))
            return false;
        if (b < 0.0 && keel::floor(ex) != ex)
            return false;
        if (b == 0.0 && ex <= 0.0)
            return false;
        res = keel::pow(b, ex);
        if (!keel::is_finite(res))
            return false;
        break;
    }
    case NodeKind::Func: {
        const keel::String &fn = c.funcName(e);
        if (c.childCount(e) == 4 && fn == "hypergeom2F1") {
            keel::f64 a0 = 0.0, a1 = 0.0, a2 = 0.0, a3 = 0.0;
            if (!evalDoubleRec(c, c.child(e, 0), vals, memo, a0) ||
                !evalDoubleRec(c, c.child(e, 1), vals, memo, a1) ||
                !evalDoubleRec(c, c.child(e, 2), vals, memo, a2) ||
                !evalDoubleRec(c, c.child(e, 3), vals, memo, a3) ||
                !evalHypergeom2F1Double(a0, a1, a2, a3, res)) {
                return false;
            }
            break;
        }
        if (c.childCount(e) == 3 && fn == "hypergeom1F1") {
            keel::f64 a0 = 0.0, a1 = 0.0, a2 = 0.0;
            if (!evalDoubleRec(c, c.child(e, 0), vals, memo, a0) ||
                !evalDoubleRec(c, c.child(e, 1), vals, memo, a1) ||
                !evalDoubleRec(c, c.child(e, 2), vals, memo, a2) ||
                !evalHypergeom1F1Double(a0, a1, a2, res)) {
                return false;
            }
            break;
        }
        if (c.childCount(e) == 2) {
            keel::f64 a0 = 0.0, a1 = 0.0;
            if (!evalDoubleRec(c, c.child(e, 0), vals, memo, a0) ||
                !evalDoubleRec(c, c.child(e, 1), vals, memo, a1))
                return false;
            if (fn == "besselj") {
                if (!evalBesselJDouble(a0, a1, res)) return false;
            } else if (fn == "bessely") {
                if (!evalBesselYDouble(a0, a1, res)) return false;
            } else if (fn == "besseli") {
                if (!evalBesselIDouble(a0, a1, res)) return false;
            } else if (fn == "besselk") {
                if (!evalBesselKDouble(a0, a1, res)) return false;
            } else if (fn == "legendreP" || fn == "chebyshevT" ||
                       fn == "chebyshevU" || fn == "hermiteH" ||
                       fn == "laguerreL") {
                if (!evalOrthogonalPolyDouble(fn, a0, a1, res)) return false;
            } else if (fn == "ellipticF" || fn == "ellipticEInc" ||
                       fn == "ellipticE" || fn == "ellipticPi") {
                if (!evalElliptic2ArgDouble(fn, a0, a1, res)) return false;
            } else if (fn == "polylog") {
                if (!evalPolylogDouble(a0, a1, res)) return false;
            } else if (fn == "bernoulliB" || fn == "eulerE") {
                if (!evalBernoulliEuler2ArgDouble(fn, a0, a1, res)) return false;
            } else if (fn == "beta") {
                if (!evalBetaDouble(a0, a1, res)) return false;
            } else if (fn == "pochhammer") {
                if (!evalPochhammerDouble(a0, a1, res)) return false;
            } else if (fn == "igamma" || fn == "gammainc") {
                if (!evalIncompleteGammaDouble(fn, a0, a1, res)) return false;
            } else if (fn == "hypergeom0F1") {
                if (!evalHypergeom0F1Double(a0, a1, res)) return false;
            } else if (fn == "stirlingS1" || fn == "stirlingS2") {
                if (keel::floor(a0) != a0 || keel::floor(a1) != a1 ||
                    a0 < 0.0 || a0 > 50.0)
                    return false;
                const auto nInt = keel::as<keel::i64>(a0);
                const auto kInt = keel::as<keel::i64>(a1);
                if (kInt < 0 || kInt > nInt) {
                    res = 0.0;
                } else if (nInt == 0 && kInt == 0) {
                    res = 1.0;
                } else if (kInt == 0) {
                    res = 0.0;
                } else {
                    keel::Array<BigInt> row(
                        kInt + 1, BigInt(0));
                    row[0] = BigInt(1);
                    for (keel::i64 i = 1; i <= nInt; ++i) {
                        const keel::i64 jMax = keel::min(i, kInt);
                        for (keel::i64 j = jMax; j >= 1; --j) {
                            const auto ju = keel::as<keel::usize>(j);
                            if (fn == "stirlingS1") {
                                row[ju] =
                                    row[ju - 1] - BigInt(i - 1) * row[ju];
                            } else {
                                row[ju] = BigInt(j) * row[ju] + row[ju - 1];
                            }
                        }
                        row[0] = BigInt(0);
                    }
                    res = Rational(row[keel::as<keel::usize>(kInt)],
                                   BigInt(1))
                              .toDouble();
                }
            } else {
                return false;
            }
            if (!keel::is_finite(res))
                return false;
            break;
        }
        keel::f64 a = 0.0;
        if (!evalDoubleRec(c, c.child(e, 0), vals, memo, a))
            return false;
        if (fn == "exp") {
            res = keel::exp(a);
        } else if (fn == "log") {
            if (a <= 0.0) return false;
            res = keel::log(a);
        } else if (fn == "sqrt") {
            if (a < 0.0) return false;
            res = keel::sqrt(a);
        } else if (fn == "abs") {
            res = keel::abs(a);
        } else if (fn == "heaviside") {
            res = (a > 0.0) ? 1.0 : ((a < 0.0) ? 0.0 : 0.5);
        } else if (fn == "sign") {
            res = (a > 0.0) ? 1.0 : ((a < 0.0) ? -1.0 : 0.0);
        } else if (fn == "sin") {
            res = keel::sin(a);
        } else if (fn == "cos") {
            res = keel::cos(a);
        } else if (fn == "tan") {
            res = keel::tan(a);
        } else if (fn == "cot") {
            const keel::f64 t = keel::tan(a);
            if (t == 0.0) return false;
            res = 1.0 / t;
        } else if (fn == "sec") {
            const keel::f64 cs = keel::cos(a);
            if (cs == 0.0) return false;
            res = 1.0 / cs;
        } else if (fn == "csc") {
            const keel::f64 sn = keel::sin(a);
            if (sn == 0.0) return false;
            res = 1.0 / sn;
        } else if (fn == "asin") {
            if (a < -1.0 || a > 1.0) return false;
            res = keel::asin(a);
        } else if (fn == "acos") {
            if (a < -1.0 || a > 1.0) return false;
            res = keel::acos(a);
        } else if (fn == "atan") {
            res = keel::atan(a);
        } else if (fn == "acot") {
            res = (a >= 0.0) ? keel::atan(1.0 / a)
                             : (keel::kPi +
                                keel::atan(1.0 / a));
        } else if (fn == "asec") {
            if (a > -1.0 && a < 1.0) return false;
            res = keel::acos(1.0 / a);
        } else if (fn == "acsc") {
            if (a > -1.0 && a < 1.0) return false;
            res = keel::asin(1.0 / a);
        } else if (fn == "sinh") {
            res = keel::sinh(a);
        } else if (fn == "cosh") {
            res = keel::cosh(a);
        } else if (fn == "tanh") {
            res = keel::tanh(a);
        } else if (fn == "coth") {
            const keel::f64 th = keel::tanh(a);
            if (th == 0.0) return false;
            res = 1.0 / th;
        } else if (fn == "sech") {
            res = 1.0 / keel::cosh(a);
        } else if (fn == "csch") {
            const keel::f64 sh = keel::sinh(a);
            if (sh == 0.0) return false;
            res = 1.0 / sh;
        } else if (fn == "asinh") {
            res = keel::asinh(a);
        } else if (fn == "acosh") {
            if (a < 1.0) return false;
            res = keel::acosh(a);
        } else if (fn == "atanh") {
            if (a <= -1.0 || a >= 1.0) return false;
            res = keel::atanh(a);
        } else if (fn == "acoth") {
            if (a >= -1.0 && a <= 1.0) return false;
            res = keel::atanh(1.0 / a);
        } else if (fn == "asech") {
            if (a <= 0.0 || a > 1.0) return false;
            res = keel::acosh(1.0 / a);
        } else if (fn == "acsch") {
            if (a == 0.0) return false;
            res = keel::asinh(1.0 / a);
        } else if (fn == "erf") {
            res = keel::erf(a);
        } else if (fn == "erfc") {
            res = keel::erfc(a);
        } else if (fn == "erfi") {
            res = evalErfiDouble(a);
        } else if (fn == "Ei") {
            if (!evalEiDouble(a, res)) return false;
        } else if (fn == "li") {
            if (a == 0.0) {
                res = 0.0;
            } else {
                if (a < 0.0 || a == 1.0) return false;
                if (!evalEiDouble(keel::log(a), res)) return false;
            }
        } else if (fn == "Si") {
            res = evalSiDouble(a);
        } else if (fn == "Ci") {
            if (!evalCiDouble(a, res)) return false;
        } else if (fn == "FresnelS") {
            res = evalFresnelDouble(a, true);
        } else if (fn == "FresnelC") {
            res = evalFresnelDouble(a, false);
        } else if (fn == "dilog" || fn == "Li2" || fn == "polylog2") {
            if (!evalDilogDouble(a, res)) return false;
        } else if (fn == "gamma") {
            if (a <= 0.0 && keel::floor(a) == a) return false;
            res = keel::tgamma(a);
        } else if (fn == "factorial") {
            if (a < 0.0 && keel::floor(a) == a) return false;
            res = keel::tgamma(a + 1.0);
        } else if (fn == "lgamma" || fn == "loggamma") {
            if (a <= 0.0) return false;
            res = keel::lgamma(a);
        } else if (fn == "digamma" || fn == "psi") {
            if (!evalDigammaDouble(a, res)) return false;
        } else if (fn == "trigamma") {
            if (!evalTrigammaDouble(a, res)) return false;
        } else if (fn == "airyAi" || fn == "airyBi" ||
                   fn == "airyAiPrime" || fn == "airyBiPrime") {
            if (!evalAiryDouble(fn, a, res)) return false;
        } else if (fn == "ellipticK" || fn == "ellipticE") {
            if (!evalElliptic1ArgDouble(fn, a, res)) return false;
        } else if (fn == "zeta") {
            if (!evalZetaDouble(a, res)) return false;
        } else if (fn == "dirichletEta") {
            if (!evalDirichletEtaDouble(a, res)) return false;
        } else if (fn == "bernoulliB" || fn == "eulerE") {
            if (keel::floor(a) != a) return false;
            Rational rVal;
            const keel::i64 nInt = keel::as<keel::i64>(a);
            if (!(fn == "bernoulliB" ? bernoulliExact(nInt, rVal)
                                     : eulerExact(nInt, rVal)))
                return false;
            res = rVal.toDouble();
        } else {
            return false;
        }
        if (!keel::is_finite(res))
            return false;
        break;
    }
    case NodeKind::Add:
    case NodeKind::Mul: {
        const bool isAdd = (c.kind(e) == NodeKind::Add);
        res = isAdd ? 0.0 : 1.0;
        for (keel::usize i = 0; i < c.childCount(e); ++i) {
            keel::f64 t = 0.0;
            if (!evalDoubleRec(c, c.child(e, i), vals, memo, t))
                return false;
            res = isAdd ? (res + t) : (res * t);
            if (!keel::is_finite(res))
                return false;
        }
        break;
    }
    }

    memo.try_insert(nid, res);
    out = res;
    return true;
}

} // namespace

bool Ctx::evalDouble(
    Expr e, keel::ArrayRef<keel::Pair<keel::StringRef, keel::f64>> vals,
    keel::f64 &out) const
{
    keel::HashMap<keel::u32, keel::f64> memo;
    return evalDoubleRec(*this, e, vals, memo, out);
}

namespace {

// Sum-of-terms view of an expression for the distributive step:
// an Add contributes its children, everything else is one term.
void pushSumTerms(const Ctx &c, Expr e, keel::Array<Expr> &out)
{
    if (c.kind(e) == NodeKind::Add) {
        for (keel::usize i = 0; i < c.childCount(e); ++i)
            out.push_back(c.child(e, i));
    } else {
        out.push_back(e);
    }
}

} // namespace

Expr Ctx::expand(Expr e)
{
    switch (kind(e)) {
    case NodeKind::Number:
    case NodeKind::Symbol:
    case NodeKind::RootOf:
        return e;
    case NodeKind::Func: {
        keel::Array<Expr> args;
        args.reserve(childCount(e));
        for (keel::usize i = 0; i < childCount(e); ++i)
            args.push_back(expand(child(e, i)));
        const keel::String &fn = funcName(e);
        if (args.size() == 2 && kind(args[0]) == NodeKind::Number) {
            const Rational &rn = numberValue(args[0]);
            keel::i64 n = 0;
            if (rn.den() == BigInt(1) && rn.num().fitsInt64(n)) {
                const Expr xArg = args[1];
                if (fn == "legendreP") {
                    if (n < 0) n = -n - 1;
                    if (n >= 0 && n <= 64) {
                        if (n == 0) return one();
                        if (n == 1) return xArg;
                        Expr pPrev = one(), pCur = xArg;
                        for (keel::i64 k = 1; k < n; ++k) {
                            const Expr pNext = expand(mul({
                                number(Rational(1, BigInt(k + 1))),
                                add({mul({number(2 * k + 1), xArg, pCur}),
                                     neg(mul({number(k), pPrev}))})}));
                            pPrev = pCur;
                            pCur = pNext;
                        }
                        return pCur;
                    }
                } else if (fn == "chebyshevT") {
                    if (n < 0) n = -n;
                    if (n >= 0 && n <= 64) {
                        if (n == 0) return one();
                        if (n == 1) return xArg;
                        Expr tPrev = one(), tCur = xArg;
                        for (keel::i64 k = 1; k < n; ++k) {
                            const Expr tNext = expand(
                                add({mul({number(2), xArg, tCur}), neg(tPrev)}));
                            tPrev = tCur;
                            tCur = tNext;
                        }
                        return tCur;
                    }
                } else if (fn == "chebyshevU") {
                    Expr sgn = one();
                    if (n == -1) return zero();
                    if (n < -1) { n = -n - 2; sgn = number(-1); }
                    if (n >= 0 && n <= 64) {
                        if (n == 0) return sgn;
                        if (n == 1) return expand(mul({sgn, number(2), xArg}));
                        Expr uPrev = one(), uCur = expand(mul({number(2), xArg}));
                        for (keel::i64 k = 1; k < n; ++k) {
                            const Expr uNext = expand(
                                add({mul({number(2), xArg, uCur}), neg(uPrev)}));
                            uPrev = uCur;
                            uCur = uNext;
                        }
                        return expand(mul({sgn, uCur}));
                    }
                } else if (fn == "hermiteH") {
                    if (n >= 0 && n <= 64) {
                        if (n == 0) return one();
                        if (n == 1) return expand(mul({number(2), xArg}));
                        Expr hPrev = one(), hCur = expand(mul({number(2), xArg}));
                        for (keel::i64 k = 1; k < n; ++k) {
                            const Expr hNext = expand(add({
                                mul({number(2), xArg, hCur}),
                                neg(mul({number(2 * k), hPrev}))}));
                            hPrev = hCur;
                            hCur = hNext;
                        }
                        return hCur;
                    }
                } else if (fn == "laguerreL") {
                    if (n >= 0 && n <= 64) {
                        if (n == 0) return one();
                        if (n == 1) return expand(add({one(), neg(xArg)}));
                        Expr lPrev = one(), lCur = expand(add({one(), neg(xArg)}));
                        for (keel::i64 k = 1; k < n; ++k) {
                            const Expr lNext = expand(mul({
                                number(Rational(1, BigInt(k + 1))),
                                add({mul({add({number(2 * k + 1), neg(xArg)}), lCur}),
                                     neg(mul({number(k), lPrev}))})}));
                            lPrev = lCur;
                            lCur = lNext;
                        }
                        return lCur;
                    }
                } else if (fn == "bernoulliB" && n >= 0 && n <= 40) {
                    keel::Array<Expr> terms;
                    BigInt binom(1);
                    for (keel::i64 k = 0; k <= n; ++k) {
                        if (k > 0)
                            binom = (binom * BigInt(n - k + 1)) / BigInt(k);
                        Rational bk;
                        if (bernoulliExact(k, bk) && !bk.isZero()) {
                            const Rational coef =
                                Rational(binom, BigInt(1)) * bk;
                            const Expr xPow = pow(xArg, number(n - k));
                            terms.push_back(mul({number(coef), xPow}));
                        }
                    }
                    return terms.empty() ? zero() : expand(add(terms));
                } else if (fn == "eulerE" && n >= 0 && n <= 40) {
                    const Expr xShift =
                        add({xArg, number(Rational(-1, BigInt(2)))});
                    keel::Array<Expr> terms;
                    BigInt binom(1);
                    for (keel::i64 k = 0; k <= n; ++k) {
                        if (k > 0)
                            binom = (binom * BigInt(n - k + 1)) / BigInt(k);
                        Rational ek;
                        if (eulerExact(k, ek) && !ek.isZero()) {
                            const BigInt twoPow = BigInt::powUInt(
                                BigInt(2), keel::as<keel::usize>(k));
                            const Rational coef =
                                Rational(binom, twoPow) * ek;
                            const Expr xPow = pow(xShift, number(n - k));
                            terms.push_back(mul({number(coef), xPow}));
                        }
                    }
                    return terms.empty() ? zero() : expand(add(terms));
                } else if ((fn == "igamma" || fn == "gammainc") && n >= 1 &&
                           n <= 20) {
                    BigInt nFact(1);
                    for (keel::i64 k = 2; k <= n - 1; ++k)
                        nFact = nFact * BigInt(k);
                    keel::Array<Expr> sumTerms;
                    BigInt kFact(1);
                    for (keel::i64 k = 0; k < n; ++k) {
                        if (k >= 2)
                            kFact = kFact * BigInt(k);
                        sumTerms.push_back(
                            mul({number(Rational(BigInt(1), kFact)),
                                 pow(xArg, number(k))}));
                    }
                    const Expr igVal = mul({
                        number(Rational(nFact, BigInt(1))),
                        func("exp", neg(xArg)),
                        add(sumTerms)});
                    if (fn == "igamma")
                        return expand(igVal);
                    return expand(add({
                        number(Rational(nFact, BigInt(1))),
                        neg(igVal)}));
                }
            }
        }
        if (args.size() == 2 && fn == "pochhammer" &&
            kind(args[1]) == NodeKind::Number &&
            numberValue(args[1]).den() == BigInt(1)) {
            keel::i64 kCount = 0;
            if (numberValue(args[1]).num().fitsInt64(kCount) &&
                keel::abs(kCount) <= 20) {
                if (kCount == 0)
                    return one();
                if (kCount > 0) {
                    keel::Array<Expr> factors;
                    factors.reserve(kCount);
                    for (keel::i64 j = 0; j < kCount; ++j)
                        factors.push_back(add({args[0], number(j)}));
                    return expand(mul(factors));
                }
                keel::Array<Expr> denFactors;
                bool okDen = true;
                for (keel::i64 j = 1; j <= -kCount; ++j) {
                    const Expr step = add({args[0], number(-j)});
                    if (isZero(step)) {
                        okDen = false;
                        break;
                    }
                    denFactors.push_back(step);
                }
                if (okDen)
                    return pow(expand(mul(denFactors)), number(-1));
            }
        }
        if (args.size() == 2 && fn == "beta") {
            for (keel::i32 side = 0; side < 2; ++side) {
                const Expr nSide = args[keel::as<keel::usize>(side)];
                const Expr xSide = args[keel::as<keel::usize>(1 - side)];
                if (kind(nSide) == NodeKind::Number &&
                    numberValue(nSide).den() == BigInt(1)) {
                    keel::i64 nInt = 0;
                    if (numberValue(nSide).num().fitsInt64(nInt) &&
                        nInt >= 1 && nInt <= 20) {
                        BigInt fact(1);
                        keel::Array<Expr> denFactors;
                        bool okDen = true;
                        for (keel::i64 k = 0; k < nInt; ++k) {
                            if (k >= 2)
                                fact = fact * BigInt(k);
                            const Expr step = add({xSide, number(k)});
                            if (isZero(step)) {
                                okDen = false;
                                break;
                            }
                            denFactors.push_back(step);
                        }
                        if (okDen) {
                            return mul({
                                number(Rational(fact, BigInt(1))),
                                pow(expand(mul(denFactors)), number(-1))});
                        }
                    }
                }
            }
        }
        if (args.size() == 3 && fn == "hypergeom1F1" &&
                   kind(args[0]) == NodeKind::Number &&
                   numberValue(args[0]).den() == BigInt(1) &&
                   numberValue(args[0]).signum() <= 0) {
            keel::i64 ma = 0;
            if (numberValue(args[0]).num().fitsInt64(ma) && -ma <= 12) {
                const keel::i64 mTerm = -ma;
                keel::Array<Expr> terms{one()};
                Expr numPoch = one();
                Expr denPoch = one();
                BigInt fact(1);
                bool okDen = true;
                for (keel::i64 k = 1; k <= mTerm; ++k) {
                    const Expr bShift = add({args[1], number(k - 1)});
                    if (isZero(bShift)) {
                        okDen = false;
                        break;
                    }
                    numPoch = mul({numPoch, add({args[0], number(k - 1)})});
                    denPoch = mul({denPoch, bShift});
                    fact = fact * BigInt(k);
                    terms.push_back(mul({
                        numPoch, pow(denPoch, number(-1)),
                        number(Rational(BigInt(1), fact)),
                        pow(args[2], number(k))}));
                }
                if (okDen)
                    return expand(add(terms));
            }
        } else if (args.size() == 4 && fn == "hypergeom2F1") {
            keel::i64 mTerm = -1;
            for (keel::usize idx = 0; idx < 2; ++idx) {
                if (kind(args[idx]) == NodeKind::Number &&
                    numberValue(args[idx]).den() == BigInt(1) &&
                    numberValue(args[idx]).signum() <= 0) {
                    keel::i64 mv = 0;
                    if (numberValue(args[idx]).num().fitsInt64(mv) &&
                        -mv <= 12 && (mTerm < 0 || -mv < mTerm)) {
                        mTerm = -mv;
                    }
                }
            }
            if (mTerm >= 0) {
                keel::Array<Expr> terms{one()};
                Expr aPoch = one(), bPoch = one(), cPoch = one();
                BigInt fact(1);
                bool okDen = true;
                for (keel::i64 k = 1; k <= mTerm; ++k) {
                    const Expr cShift = add({args[2], number(k - 1)});
                    if (isZero(cShift)) {
                        okDen = false;
                        break;
                    }
                    aPoch = mul({aPoch, add({args[0], number(k - 1)})});
                    bPoch = mul({bPoch, add({args[1], number(k - 1)})});
                    cPoch = mul({cPoch, cShift});
                    fact = fact * BigInt(k);
                    terms.push_back(mul({
                        aPoch, bPoch, pow(cPoch, number(-1)),
                        number(Rational(BigInt(1), fact)),
                        pow(args[3], number(k))}));
                }
                if (okDen)
                    return expand(add(terms));
            }
        }
        return func(fn, args);
    }
    case NodeKind::Pow: {
        const Expr base = expand(child(e, 0));
        const Expr exp = child(e, 1);
        keel::i64 k = 0;
        const bool intExp = kind(exp) == NodeKind::Number &&
                            numberValue(exp).den() == BigInt(1) &&
                            numberValue(exp).num().fitsInt64(k);
        if (!intExp)
            return pow(base, exp);
        // (sum)^k with k >= 2: distribute by iterated multiplication;
        // k <= 1 canonicalizes away already. Negative k distributes
        // multiplicatively over the base factors instead.
        if (k <= 1)
            return pow(base, exp);
        keel::Array<Expr> terms{one()};
        keel::Array<Expr> factors;
        for (keel::i32 i = 0; i < k; ++i) {
            factors.clear();
            pushSumTerms(*this, base, factors);
            keel::Array<Expr> next;
            next.reserve(terms.size() * factors.size());
            for (const Expr &t : terms) {
                for (const Expr &f : factors) {
                    const Expr prod = mul({t, f});
                    bool hasAddFactor = (kind(prod) == NodeKind::Add);
                    if (kind(prod) == NodeKind::Mul) {
                        for (keel::usize j = 0; j < childCount(prod); ++j) {
                            if (kind(child(prod, j)) == NodeKind::Add) {
                                hasAddFactor = true;
                                break;
                            }
                        }
                    }
                    if (hasAddFactor)
                        pushSumTerms(*this, expand(prod), next);
                    else
                        next.push_back(prod);
                }
            }
            terms = keel::move(next);
        }
        return add(terms);
    }
    case NodeKind::Add: {
        keel::Array<Expr> kids;
        for (keel::usize i = 0; i < childCount(e); ++i)
            pushSumTerms(*this, expand(child(e, i)), kids);
        return add(kids);
    }
    case NodeKind::Mul: {
        // Multiply out the sum-views of the expanded factors.
        keel::Array<Expr> terms{one()};
        for (keel::usize i = 0; i < childCount(e); ++i) {
            keel::Array<Expr> factors;
            pushSumTerms(*this, expand(child(e, i)), factors);
            keel::Array<Expr> next;
            next.reserve(terms.size() * factors.size());
            for (const Expr &t : terms) {
                for (const Expr &f : factors) {
                    const Expr prod = mul({t, f});
                    bool hasAddFactor = (kind(prod) == NodeKind::Add);
                    if (kind(prod) == NodeKind::Mul) {
                        for (keel::usize j = 0; j < childCount(prod); ++j) {
                            if (kind(child(prod, j)) == NodeKind::Add) {
                                hasAddFactor = true;
                                break;
                            }
                        }
                    }
                    if (hasAddFactor)
                        pushSumTerms(*this, expand(prod), next);
                    else
                        next.push_back(prod);
                }
            }
            terms = keel::move(next);
        }
        return add(terms);
    }
    }
    return e;
}

Expr Ctx::subs(Expr e, Expr from, Expr to)
{
    if (e == from)
        return to;
    switch (kind(e)) {
    case NodeKind::Number:
    case NodeKind::Symbol:
    case NodeKind::RootOf:
        return e; // atoms: no children to descend into
    case NodeKind::Func: {
        // Evaluating an abstract symbolic derivative at a point (e.g.
        // subs(diff(y(t), t), t, 0) or Dy(0)): preserve as unevaluated
        // subs(diff(y(t), t), t, 0) so differentiation variable isn't
        // replaced by a constant and y(0) substitutions don't corrupt it.
        if (funcName(e) == "diff" && (childCount(e) == 2 || childCount(e) == 3) &&
            child(e, 1) == from && from != to) {
            return func("subs", {e, from, to});
        }
        keel::Array<Expr> kids;
        kids.reserve(childCount(e));
        for (keel::usize i = 0; i < childCount(e); ++i)
            kids.push_back(subs(child(e, i), from, to));
        return func(funcName(e), kids);
    }
    case NodeKind::Pow:
        return pow(subs(child(e, 0), from, to),
                   subs(child(e, 1), from, to));
    case NodeKind::Add:
    case NodeKind::Mul: {
        keel::Array<Expr> kids;
        kids.reserve(childCount(e));
        for (keel::usize i = 0; i < childCount(e); ++i)
            kids.push_back(subs(child(e, i), from, to));
        return kind(e) == NodeKind::Add ? add(kids) : mul(kids);
    }
    }
    return e;
}

keel::String Ctx::toString(Expr e) const
{
    keel::String out;
    print(e, out);
    return out;
}

keel::usize Ctx::leafCount(Expr e) const
{
    if (e.isNull())
        return 0;
    switch (kind(e)) {
    case NodeKind::Number:
    case NodeKind::Symbol:
    case NodeKind::RootOf:
        return 1;
    case NodeKind::Pow:
    case NodeKind::Func:
    case NodeKind::Add:
    case NodeKind::Mul: {
        keel::usize total = 1;
        for (keel::usize i = 0; i < childCount(e); ++i)
            total += leafCount(child(e, i));
        return total;
    }
    }
    return 1;
}

namespace {

bool isElementaryFuncName(keel::StringRef name)
{
    return name == "log" || name == "exp" || name == "abs" ||
           name == "sin" || name == "cos" || name == "tan" ||
           name == "cot" || name == "sec" || name == "csc" ||
           name == "asin" || name == "acos" || name == "atan" ||
           name == "acot" || name == "asec" || name == "acsc" ||
           name == "sinh" || name == "cosh" || name == "tanh" ||
           name == "coth" || name == "sech" || name == "csch" ||
           name == "asinh" || name == "acosh" || name == "atanh" ||
           name == "acoth" || name == "asech" || name == "acsch";
}

} // namespace

keel::usize Ctx::exprCost(Expr e) const
{
    if (e.isNull())
        return 0;
    keel::HashMap<keel::u32, bool> visited;
    keel::usize total = 0;

    struct Frame
    {
        Expr expr;
        bool insideLog;
    };
    keel::Array<Frame> stack{Frame{e, false}};
    while (!stack.empty()) {
        const Frame cur = stack.back();
        stack.pop_back();
        if (cur.expr.isNull())
            continue;
        const keel::u32 nid = id(cur.expr);
        if (bool *flag = visited.get(nid)) {
            // If an `abs` node was previously visited outside `log` (cost 3)
            // and is now also reached directly inside `log` (cost 5), upgrade
            // its weight by +2 once.
            if (cur.insideLog && !(*flag) &&
                kind(cur.expr) == NodeKind::Func &&
                funcName(cur.expr) == "abs") {
                *flag = true;
                total += 2;
            }
            continue;
        }
        const NodeKind k = kind(cur.expr);
        bool markedInsideLog = false;
        if (k == NodeKind::Func) {
            const keel::String &fn = funcName(cur.expr);
            if (cur.insideLog && fn == "abs") {
                total += 5;
                markedInsideLog = true;
            } else if (isElementaryFuncName(fn)) {
                total += 3;
            } else {
                total += 10;
            }
        } else {
            total += 1;
        }
        visited.try_insert(nid, markedInsideLog);
        const bool nextInsideLog =
            (k == NodeKind::Func && funcName(cur.expr) == "log");
        for (keel::usize i = 0; i < childCount(cur.expr); ++i)
            stack.push_back(Frame{child(cur.expr, i), nextInsideLog});
    }
    return total;
}

void Ctx::assume(keel::StringRef name, AssumeDomain dom)
{
    if (dom == AssumeDomain::Any)
        assumptions_.remove(name);
    else
        assumptions_.put(keel::String::from(name), dom);
}

void Ctx::assume(Expr sym, AssumeDomain dom)
{
    assert(!sym.isNull() && kind(sym) == NodeKind::Symbol);
    if (!sym.isNull() && kind(sym) == NodeKind::Symbol)
        assume(symbolName(sym), dom);
}

AssumeDomain Ctx::assumption(keel::StringRef name) const
{
    if (const AssumeDomain *hit = assumptions_.get(name))
        return *hit;
    return AssumeDomain::Any;
}

AssumeDomain Ctx::assumption(Expr sym) const
{
    assert(!sym.isNull() && kind(sym) == NodeKind::Symbol);
    if (sym.isNull() || kind(sym) != NodeKind::Symbol)
        return AssumeDomain::Any;
    return assumption(symbolName(sym));
}

void Ctx::clearAssumptions()
{
    assumptions_.clear();
}

bool Ctx::isAssumedPositive(Expr e) const
{
    if (e.isNull())
        return false;
    switch (kind(e)) {
    case NodeKind::Number:
        return numberValue(e).signum() > 0;
    case NodeKind::Symbol: {
        const keel::String &nm = symbolName(e);
        const AssumeDomain dom = assumption(nm);
        if (dom != AssumeDomain::Any)
            return dom == AssumeDomain::Positive;
        return nm == "pi" || nm == "e" || nm == "E" || nm == "euler_gamma" ||
               nm == "EulerGamma";
    }
    case NodeKind::RootOf:
        return false;
    case NodeKind::Pow: {
        const Expr b = child(e, 0);
        const Expr ex = child(e, 1);
        if (isAssumedPositive(b) && isAssumedReal(ex))
            return true;
        if (kind(ex) == NodeKind::Number) {
            const Rational &re = numberValue(ex);
            if (re.den() == BigInt(1) && (re.num() % BigInt(2)).isZero() &&
                isAssumedNegative(b)) {
                return true;
            }
        }
        return false;
    }
    case NodeKind::Func: {
        const keel::String &fn = funcName(e);
        const Expr u = child(e, 0);
        if (fn == "exp" || fn == "cosh" || fn == "sech" || fn == "erfc")
            return isAssumedReal(u);
        if (fn == "abs")
            return isAssumedPositive(u) || isAssumedNegative(u);
        if (fn == "factorial")
            return isAssumedNonNegative(u);
        if (fn == "sqrt" || fn == "sinh" || fn == "tanh" || fn == "asinh" ||
            fn == "atan" || fn == "erf" || fn == "erfi" || fn == "Si" ||
            fn == "FresnelS" || fn == "FresnelC" || fn == "gamma" ||
            fn == "trigamma")
            return isAssumedPositive(u);
        return false;
    }
    case NodeKind::Mul: {
        keel::i32 sign = 1;
        for (keel::usize i = 0; i < childCount(e); ++i) {
            const Expr ch = child(e, i);
            if (isAssumedPositive(ch))
                continue;
            if (isAssumedNegative(ch))
                sign = -sign;
            else
                return false;
        }
        return sign > 0;
    }
    case NodeKind::Add: {
        bool anyPos = false;
        for (keel::usize i = 0; i < childCount(e); ++i) {
            const Expr ch = child(e, i);
            if (isAssumedPositive(ch))
                anyPos = true;
            else if (!isAssumedNonNegative(ch))
                return false;
        }
        return anyPos;
    }
    }
    return false;
}

bool Ctx::isAssumedNegative(Expr e) const
{
    if (e.isNull())
        return false;
    switch (kind(e)) {
    case NodeKind::Number:
        return numberValue(e).signum() < 0;
    case NodeKind::Symbol:
        return assumption(symbolName(e)) == AssumeDomain::Negative;
    case NodeKind::RootOf:
        return false;
    case NodeKind::Pow: {
        const Expr b = child(e, 0);
        const Expr ex = child(e, 1);
        if (kind(ex) == NodeKind::Number) {
            const Rational &re = numberValue(ex);
            if (re.den() == BigInt(1) && !(re.num() % BigInt(2)).isZero() &&
                isAssumedNegative(b)) {
                return true;
            }
        }
        return false;
    }
    case NodeKind::Func: {
        const keel::String &fn = funcName(e);
        const Expr u = child(e, 0);
        if (fn == "sinh" || fn == "tanh" || fn == "asinh" || fn == "atan" ||
            fn == "erf" || fn == "erfi" || fn == "Si" || fn == "FresnelS" ||
            fn == "FresnelC")
            return isAssumedNegative(u);
        return false;
    }
    case NodeKind::Mul: {
        keel::i32 sign = 1;
        for (keel::usize i = 0; i < childCount(e); ++i) {
            const Expr ch = child(e, i);
            if (isAssumedPositive(ch))
                continue;
            if (isAssumedNegative(ch))
                sign = -sign;
            else
                return false;
        }
        return sign < 0;
    }
    case NodeKind::Add: {
        bool anyNeg = false;
        for (keel::usize i = 0; i < childCount(e); ++i) {
            const Expr ch = child(e, i);
            if (isAssumedNegative(ch))
                anyNeg = true;
            else if (!isZero(ch))
                return false;
        }
        return anyNeg;
    }
    }
    return false;
}

bool Ctx::isAssumedNonNegative(Expr e) const
{
    if (e.isNull())
        return false;
    if (isZero(e) || isAssumedPositive(e))
        return true;
    switch (kind(e)) {
    case NodeKind::Number:
        return numberValue(e).signum() >= 0;
    case NodeKind::Symbol: {
        const AssumeDomain dom = assumption(symbolName(e));
        return dom == AssumeDomain::NonNegative || dom == AssumeDomain::Positive;
    }
    case NodeKind::RootOf:
        return false;
    case NodeKind::Pow: {
        const Expr b = child(e, 0);
        const Expr ex = child(e, 1);
        if (kind(ex) == NodeKind::Number) {
            const Rational &re = numberValue(ex);
            if (re.signum() > 0 && isAssumedNonNegative(b))
                return true;
            if (re.den() == BigInt(1) && re.signum() >= 0 &&
                (re.num() % BigInt(2)).isZero() && isAssumedReal(b))
                return true;
        }
        return false;
    }
    case NodeKind::Func: {
        const keel::String &fn = funcName(e);
        const Expr u = child(e, 0);
        if (fn == "abs")
            return isAssumedReal(u);
        if (fn == "sqrt" || fn == "sinh" || fn == "tanh" || fn == "asinh" ||
            fn == "atan" || fn == "erf" || fn == "erfi" || fn == "Si" ||
            fn == "FresnelS" || fn == "FresnelC")
            return isAssumedNonNegative(u);
        return false;
    }
    case NodeKind::Mul: {
        keel::i32 negCount = 0;
        for (keel::usize i = 0; i < childCount(e); ++i) {
            const Expr ch = child(e, i);
            if (isAssumedNonNegative(ch))
                continue;
            if (isAssumedNegative(ch))
                ++negCount;
            else
                return false;
        }
        return (negCount % 2) == 0;
    }
    case NodeKind::Add: {
        for (keel::usize i = 0; i < childCount(e); ++i)
            if (!isAssumedNonNegative(child(e, i)))
                return false;
        return true;
    }
    }
    return false;
}

bool Ctx::isAssumedReal(Expr e) const
{
    if (e.isNull())
        return false;
    if (isAssumedNonNegative(e) || isAssumedNegative(e))
        return true;
    switch (kind(e)) {
    case NodeKind::Number:
        return true;
    case NodeKind::Symbol: {
        const keel::String &nm = symbolName(e);
        return assumption(nm) != AssumeDomain::Any || nm == "pi" ||
               nm == "e" || nm == "E" || nm == "euler_gamma" ||
               nm == "EulerGamma";
    }
    case NodeKind::RootOf:
        return false;
    case NodeKind::Pow: {
        const Expr b = child(e, 0);
        const Expr ex = child(e, 1);
        if (isAssumedPositive(b) && isAssumedReal(ex))
            return true;
        if (kind(ex) == NodeKind::Number) {
            const Rational &re = numberValue(ex);
            if (re.den() == BigInt(1) && isAssumedReal(b))
                return true;
            if (re.signum() >= 0 && isAssumedNonNegative(b))
                return true;
        }
        return false;
    }
    case NodeKind::Func: {
        const keel::String &fn = funcName(e);
        const Expr u = child(e, 0);
        if (fn == "log" || fn == "Ci" || fn == "lgamma" || fn == "loggamma" ||
            fn == "digamma" || fn == "psi" || fn == "trigamma" || fn == "gamma")
            return isAssumedPositive(u);
        if (fn == "Ei")
            return isAssumedPositive(u) || isAssumedNegative(u);
        if (fn == "sqrt")
            return isAssumedNonNegative(u);
        if (fn == "exp" || fn == "abs" || fn == "sin" || fn == "cos" ||
            fn == "tan" || fn == "cot" || fn == "sec" || fn == "csc" ||
            fn == "atan" || fn == "acot" || fn == "sinh" || fn == "cosh" ||
            fn == "tanh" || fn == "coth" || fn == "sech" || fn == "csch" ||
            fn == "asinh" || fn == "erf" || fn == "erfc" || fn == "erfi" ||
            fn == "Si" || fn == "FresnelS" || fn == "FresnelC")
            return isAssumedReal(u);
        return false;
    }
    case NodeKind::Mul:
    case NodeKind::Add: {
        for (keel::usize i = 0; i < childCount(e); ++i)
            if (!isAssumedReal(child(e, i)))
                return false;
        return true;
    }
    }
    return false;
}

bool Ctx::isAssumedInteger(Expr e) const
{
    if (e.isNull())
        return false;
    switch (kind(e)) {
    case NodeKind::Number:
        return numberValue(e).den() == BigInt(1);
    case NodeKind::Symbol:
        return assumption(symbolName(e)) == AssumeDomain::Integer;
    case NodeKind::RootOf:
    case NodeKind::Func:
        return false;
    case NodeKind::Pow: {
        const Expr b = child(e, 0);
        const Expr ex = child(e, 1);
        return isAssumedInteger(b) && isAssumedInteger(ex) &&
               isAssumedNonNegative(ex);
    }
    case NodeKind::Mul:
    case NodeKind::Add: {
        for (keel::usize i = 0; i < childCount(e); ++i)
            if (!isAssumedInteger(child(e, i)))
                return false;
        return true;
    }
    }
    return false;
}

} // namespace numkit::cas
