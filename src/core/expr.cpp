#include <numkit/cas/core/expr.hpp>

#include <algorithm>

namespace numkit::cas {

namespace {

constexpr std::uint32_t kFnvOffset = 2166136261u;
constexpr std::uint32_t kFnvPrime = 16777619u;

constexpr std::int64_t kMaxFoldExp = 65536; // numeric Pow folding bound

std::uint32_t mix32(std::uint32_t h, std::uint32_t v)
{
    return (h ^ v) * kFnvPrime;
}

std::uint32_t hashName(const std::string &s)
{
    std::uint32_t h = kFnvOffset;
    for (char c : s)
        h = mix32(h, static_cast<std::uint8_t>(c));
    return h;
}

int signOf(int c)
{
    return c < 0 ? -1 : (c > 0 ? 1 : 0);
}

// Exponent of the printing precedence ladder; larger binds tighter.
int precOf(NodeKind k, const Rational &num)
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

Expr Ctx::number(std::int64_t v)
{
    return number(Rational(v));
}

Expr Ctx::number(Rational v)
{
    return makeNode(NodeKind::Number, 0, {}, v);
}

std::uint32_t Ctx::internName(const std::string &name,
                              std::unordered_map<std::string, std::uint32_t> &ids,
                              std::deque<std::string> &names)
{
    auto it = ids.find(name);
    if (it != ids.end())
        return it->second;
    const std::uint32_t id = static_cast<std::uint32_t>(names.size());
    names.push_back(name);
    ids.emplace(names.back(), id);
    return id;
}

Expr Ctx::symbol(const std::string &name)
{
    const std::uint32_t id = internName(name, symbolIds_, symbolNames_);
    return makeNode(NodeKind::Symbol, id, {}, Rational(std::int64_t{0}));
}

Expr Ctx::func(const std::string &name, Expr arg)
{
    const std::uint32_t id = internName(name, funcIds_, funcNames_);
    return makeNode(NodeKind::Func, id, {arg}, Rational(std::int64_t{0}));
}

Expr Ctx::rootOf(std::vector<Rational> poly, int index)
{
    while (poly.size() > 1 && poly.back().isZero())
        poly.pop_back();
    assert(poly.size() >= 3 && "RootOf needs degree >= 2");
    const Rational lc = poly.back();
    assert(!(lc == Rational(std::int64_t{0})) && "RootOf of zero polynomial");
    assert(index >= 0);
    if (!(lc == Rational(std::int64_t{1})))
        for (Rational &c : poly)
            c = c / lc;
    assert(index < static_cast<int>(poly.size()) - 1);

    std::uint32_t hash = mix32(kFnvOffset, static_cast<std::uint32_t>(NodeKind::RootOf));
    hash = mix32(hash, static_cast<std::uint32_t>(index));
    for (const Rational &c : poly) {
        const std::uint64_t h64 = c.hashBits();
        hash = mix32(hash, static_cast<std::uint32_t>(h64));
        hash = mix32(hash, static_cast<std::uint32_t>(h64 >> 32));
    }
    for (const RootOfDesc &d : rootofs_) {
        if (d.index == index && d.poly == poly && d.nodeId != 0)
            return Expr(this, d.nodeId);
    }
    rootofs_.push_back(RootOfDesc{std::move(poly), index, 0});
    const auto tableIdx = static_cast<std::uint32_t>(rootofs_.size() - 1);
    const Expr made = makeNode(NodeKind::RootOf, tableIdx, {}, Rational(std::int64_t{0}));
    rootofs_[tableIdx].nodeId = id(made);
    return made;
}

const std::vector<Rational> &Ctx::rootOfPoly(Expr e) const
{
    assert(kind(e) == NodeKind::RootOf);
    return rootofs_[node(e).aux].poly;
}

int Ctx::rootOfIndex(Expr e) const
{
    assert(kind(e) == NodeKind::RootOf);
    return rootofs_[node(e).aux].index;
}

Expr Ctx::neg(Expr a)
{
    return mul({number(std::int64_t{-1}), a});
}

Expr Ctx::div(Expr a, Expr b)
{
    if (kind(b) == NodeKind::Number) {
        assert(!numberValue(b).isZero() && "division by zero constant");
        if (numberValue(b).isZero())
            return Expr(); // null in Release: no 0^-1 garbage nodes
    }
    return mul({a, pow(b, number(std::int64_t{-1}))});
}

bool Ctx::smallInteger(const Rational &e, std::int64_t &n) const
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
        if (e == Rational(std::int64_t{1}))
            return base;
        if (kind(base) == NodeKind::Number &&
            numberValue(base) == Rational(std::int64_t{1}))
            return one();

        std::int64_t n = 0;
        const bool isSmallInt = smallInteger(e, n);

        if (kind(base) == NodeKind::Number && isSmallInt) {
            const Rational &b = numberValue(base);
            if (n >= 0) {
                Rational r(BigInt::powUInt(b.num(), static_cast<std::uint64_t>(n)),
                           BigInt::powUInt(b.den(), static_cast<std::uint64_t>(n)));
                return number(r);
            }
            if (b.isZero()) {
                assert(!"zero raised to a negative power");
                return Expr(); // null in Release: no 0^-k garbage nodes
            }
            // b != 0, n < 0: (p/q)^n = q^|n| / p^|n|
            Rational r(BigInt::powUInt(b.den(), static_cast<std::uint64_t>(-n)),
                       BigInt::powUInt(b.num(), static_cast<std::uint64_t>(-n)));
            return number(r);
        }

        // (u^a)^n = u^(a*n) holds for integer n.
        if (kind(base) == NodeKind::Pow && isSmallInt &&
            kind(child(base, 1)) == NodeKind::Number) {
            return pow(child(base, 0), mul({exp, child(base, 1)}));
        }

        // (u*v)^n = u^n * v^n holds for integer n.
        if (kind(base) == NodeKind::Mul && isSmallInt) {
            std::vector<Expr> parts;
            for (std::size_t i = 0; i < childCount(base); ++i)
                parts.push_back(pow(child(base, i), exp));
            return makeMul(parts);
        }
    }
    return makeNode(NodeKind::Pow, 0, {base, exp}, Rational(std::int64_t{0}));
}

Expr Ctx::makeAdd(const std::vector<Expr> &children)
{
    // Collect like terms: every non-number child decomposes into
    // (coefficient, term) — a canonical Mul carries its numeric constant as
    // the first child — and coefficients of equal terms sum up. Run-only
    // merging would not be canonical: y + y + 2*y would fold the two y's
    // into a 2*y that then coexists with the original 2*y child.
    std::vector<std::pair<Expr, Rational>> acc;
    Rational constSum(0);
    const auto absorbTerm = [&](Expr c) {
        Rational coef(std::int64_t{1});
        Expr term = c;
        if (kind(c) == NodeKind::Mul && childCount(c) > 0 &&
            kind(child(c, 0)) == NodeKind::Number) {
            coef = numberValue(child(c, 0));
            if (childCount(c) == 2) {
                term = child(c, 1);
            } else {
                std::vector<Expr> rest;
                for (std::size_t i = 1; i < childCount(c); ++i)
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
            for (std::size_t i = 0; i < childCount(c); ++i) {
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

    std::vector<Expr> items;
    for (const auto &p : acc) {
        if (p.second.isZero())
            continue;
        items.push_back(p.second == Rational(std::int64_t{1})
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
    for (std::size_t i = 0; i < items.size(); ++i)
        for (std::size_t j = i + 1; j < items.size(); ++j)
            assert(items[i] != items[j] && "makeAdd duplicate items");
#endif
    std::sort(items.begin(), items.end(),
              [this](Expr a, Expr b) { return compare(a, b) < 0; });
    return makeNode(NodeKind::Add, 0, items, Rational(std::int64_t{0}));
}

Expr Ctx::makeMul(const std::vector<Expr> &children)
{
    // Collect like bases: every non-number child decomposes into
    // (base, exponent) — Pow with a numeric exponent — and exponents of
    // equal bases sum up. Mirrors the coefficient collection of makeAdd;
    // run-only merging would leave x * x * x^2 as x^2 * x^2.
    std::vector<std::pair<Expr, Rational>> acc;
    Rational constProd(1);
    const auto absorbBase = [&](Expr c) {
        Expr base = c;
        Rational exp(std::int64_t{1});
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
            for (std::size_t i = 0; i < childCount(c); ++i) {
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

    std::vector<Expr> items;
    for (const auto &p : acc) {
        if (p.second.isZero())
            continue;
        items.push_back(p.second == Rational(std::int64_t{1})
                            ? p.first
                            : pow(p.first, number(p.second)));
    }
    if (!(constProd == Rational(std::int64_t{1})))
        items.push_back(number(constProd));

    if (items.empty())
        return one();
    if (items.size() == 1)
        return items[0];
#ifndef NDEBUG
    for (std::size_t i = 0; i < items.size(); ++i)
        for (std::size_t j = i + 1; j < items.size(); ++j)
            assert(items[i] != items[j] && "makeMul duplicate items");
#endif
    std::sort(items.begin(), items.end(),
              [this](Expr a, Expr b) { return compare(a, b) < 0; });
    return makeNode(NodeKind::Mul, 0, items, Rational(std::int64_t{0}));
}

Expr Ctx::makeNode(NodeKind kind, std::uint32_t aux,
                   const std::vector<Expr> &children, const Rational &num)
{
    std::uint32_t hash = mix32(kFnvOffset, static_cast<std::uint32_t>(kind));
    hash = mix32(hash, aux);
    if (kind == NodeKind::Number) {
        const std::uint64_t h64 = num.hashBits();
        hash = mix32(hash, static_cast<std::uint32_t>(h64));
        hash = mix32(hash, static_cast<std::uint32_t>(h64 >> 32));
    }
    for (Expr c : children)
        hash = mix32(hash, node(c).hash);

    auto range = intern_.equal_range(hash);
    for (auto it = range.first; it != range.second; ++it) {
        const Node &n = nodes_[it->second - 1];
        if (n.hash == hash &&
            equalNode(n, kind, aux, children, num))
            return Expr(this, it->second);
    }

    Node n;
    n.kind = kind;
    n.aux = aux;
    n.childOff = static_cast<std::uint32_t>(childArena_.size());
    n.childCount = static_cast<std::uint32_t>(children.size());
    n.hash = hash;
    n.num = num;
    for (Expr c : children)
        childArena_.push_back(c.id_);

    const auto id = static_cast<std::uint32_t>(nodes_.size() + 1);
    nodes_.push_back(std::move(n));
    intern_.emplace(hash, id);
    return Expr(this, id);
}

bool Ctx::equalNode(const Node &n, NodeKind kind, std::uint32_t aux,
                    const std::vector<Expr> &children, const Rational &num) const
{
    if (n.kind != kind || n.aux != aux || n.childCount != children.size())
        return false;
    if (kind == NodeKind::Number && !(n.num == num))
        return false;
    for (std::size_t i = 0; i < children.size(); ++i)
        if (childArena_[n.childOff + i] != children[i].id_)
            return false;
    return true;
}

const std::string &Ctx::symbolName(Expr e) const
{
    assert(kind(e) == NodeKind::Symbol);
    return symbolNames_[node(e).aux];
}

const std::string &Ctx::funcName(Expr e) const
{
    assert(kind(e) == NodeKind::Func);
    return funcNames_[node(e).aux];
}

Expr Ctx::child(Expr e, std::size_t i) const
{
    const Node &n = node(e);
    assert(i < n.childCount);
    return Expr(const_cast<Ctx *>(this), childArena_[n.childOff + i]);
}

int Ctx::kindRank(NodeKind k)
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

int Ctx::compare(Expr a, Expr b) const
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
        return signOf(symbolNames_[na.aux].compare(symbolNames_[nb.aux]));
    case NodeKind::Func: {
        const int byName = funcNames_[na.aux].compare(funcNames_[nb.aux]);
        if (byName != 0)
            return signOf(byName);
        return compare(child(a, 0), child(b, 0));
    }
    case NodeKind::Pow: {
        const int byBase = compare(child(a, 0), child(b, 0));
        if (byBase != 0)
            return byBase;
        return compare(child(a, 1), child(b, 1));
    }
    case NodeKind::RootOf: {
        if (na.aux != nb.aux) {
            const RootOfDesc &da = rootofs_[na.aux];
            const RootOfDesc &db = rootofs_[nb.aux];
            const std::size_t n = std::min(da.poly.size(), db.poly.size());
            for (std::size_t i = 0; i < n; ++i)
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
        const std::size_t n = std::min(na.childCount, nb.childCount);
        for (std::size_t i = 0; i < n; ++i) {
            const int c = compare(child(a, i), child(b, i));
            if (c != 0)
                return c;
        }
        return na.childCount < nb.childCount ? -1
               : na.childCount > nb.childCount ? 1 : 0;
    }
    }
    return 0;
}

void Ctx::printPrec(Expr e, std::string &out, int parentPrec) const
{
    const Node &n = node(e);
    const int prec = precOf(n.kind, n.num);

    switch (n.kind) {
    case NodeKind::Number:
    case NodeKind::Symbol: {
        if (prec < parentPrec)
            out += '(';
        if (n.kind == NodeKind::Number)
            out += n.num.toString();
        else
            out += symbolNames_[n.aux];
        if (prec < parentPrec)
            out += ')';
        break;
    }
    case NodeKind::RootOf: {
        out += "RootOf(";
        const RootOfDesc &d = rootofs_[n.aux];
        for (std::size_t k = d.poly.size(); k-- > 0;) {
            out += d.poly[k].toString();
            if (k == 1) {
                out += "*z + ";
            } else if (k > 1) {
                out += "*z^" + std::to_string(k) + " + ";
            }
        }
        out += ", " + std::to_string(d.index) + ")";
        break;
    }
    case NodeKind::Func: {
        if (prec < parentPrec)
            out += '(';
        out += funcNames_[n.aux];
        out += '(';
        printPrec(child(e, 0), out, 0);
        out += ')';
        if (prec < parentPrec)
            out += ')';
        break;
    }
    case NodeKind::Pow: {
        if (prec < parentPrec)
            out += '(';
        // A NEGATIVE numeric base must keep parens: "-9^(1/2)" reads
        // back as -(9^(1/2)) under the parser's precedence (unary
        // minus looser than '^') — a different principal branch
        // (bugs/opened/core/expr-neg-pow-base-print.md).
        const bool negNumBase = kind(child(e, 0)) == NodeKind::Number &&
                                numberValue(child(e, 0)).num().isNegative();
        if (negNumBase)
            out += '(';
        // 61, not 60: a Pow base that is itself a Pow must keep parens
        // ("(x^2)^3" != "x^(2^3)").
        printPrec(child(e, 0), out, negNumBase ? 0 : 61);
        if (negNumBase)
            out += ')';
        out += '^';
        printPrec(child(e, 1), out, 61);
        if (prec < parentPrec)
            out += ')';
        break;
    }
    case NodeKind::Mul: {
        if (prec < parentPrec)
            out += '(';
        std::size_t start = 0;
        if (childCount(e) > 1 && kind(child(e, 0)) == NodeKind::Number &&
            numberValue(child(e, 0)) == Rational(std::int64_t{-1})) {
            out += '-';
            start = 1;
        }
        for (std::size_t i = start; i < childCount(e); ++i) {
            if (i > start)
                out += '*';
            printPrec(child(e, i), out, 50);
        }
        if (prec < parentPrec)
            out += ')';
        break;
    }
    case NodeKind::Add: {
        if (prec < parentPrec)
            out += '(';
        for (std::size_t i = 0; i < childCount(e); ++i) {
            if (i > 0)
                out += " + ";
            printPrec(child(e, i), out, 40);
        }
        if (prec < parentPrec)
            out += ')';
        break;
    }
    }
}

void Ctx::print(Expr e, std::string &out) const
{
    printPrec(e, out, 0);
}

bool Ctx::evalExact(
    Expr e, const std::vector<std::pair<std::string, Rational>> &vals,
    Rational &out)
{
    switch (kind(e)) {
    case NodeKind::Number:
        out = numberValue(e);
        return true;
    case NodeKind::Symbol: {
        const std::string &name = symbolName(e);
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
        Rational a;
        if (!evalExact(child(e, 0), vals, a))
            return false;
        const std::string &name = funcName(e);
        const Rational zero(0), one(1);
        if (name == "exp" && a == zero) { out = one; return true; }
        if (name == "log" && a == one) { out = zero; return true; }
        if ((name == "sin" || name == "tan" || name == "atan" ||
             name == "asin" || name == "sinh" || name == "tanh" ||
             name == "asinh" || name == "atanh") && a == zero) {
            out = zero;
            return true;
        }
        if ((name == "cos" || name == "cosh") && a == zero) {
            out = one;
            return true;
        }
        if ((name == "acos" || name == "acosh") && a == one) {
            out = zero;
            return true;
        }
        return false;
    }
    case NodeKind::Pow: {
        Rational base, ex;
        if (!evalExact(child(e, 0), vals, base) ||
            !evalExact(child(e, 1), vals, ex))
            return false;
        std::int64_t k = 0;
        if (!(ex.den() == BigInt(1)) || !ex.num().fitsInt64(k))
            return false; // fractional or huge exponent: irrational
        if (k >= 0) {
            out = Rational::powUInt(base, static_cast<std::uint64_t>(k));
            return true;
        }
        if (base.isZero())
            return false; // 0^negative
        out = Rational(BigInt(1), BigInt(1)) /
              Rational::powUInt(base, static_cast<std::uint64_t>(-k));
        return true;
    }
    case NodeKind::Add:
    case NodeKind::Mul: {
        Rational acc = kind(e) == NodeKind::Add
                           ? Rational(std::int64_t{0})
                           : Rational(std::int64_t{1});
        for (std::size_t i = 0; i < childCount(e); ++i) {
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

// Sum-of-terms view of an expression for the distributive step:
// an Add contributes its children, everything else is one term.
void pushSumTerms(const Ctx &c, Expr e, std::vector<Expr> &out)
{
    if (c.kind(e) == NodeKind::Add) {
        for (std::size_t i = 0; i < c.childCount(e); ++i)
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
    case NodeKind::Func:
        return func(funcName(e), expand(child(e, 0)));
    case NodeKind::Pow: {
        const Expr base = expand(child(e, 0));
        const Expr exp = child(e, 1);
        std::int64_t k = 0;
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
        std::vector<Expr> terms{one()};
        std::vector<Expr> factors;
        for (int i = 0; i < k; ++i) {
            factors.clear();
            pushSumTerms(*this, base, factors);
            std::vector<Expr> next;
            next.reserve(terms.size() * factors.size());
            for (const Expr &t : terms)
                for (const Expr &f : factors)
                    next.push_back(mul({t, f}));
            terms = std::move(next);
        }
        return add(terms);
    }
    case NodeKind::Add: {
        std::vector<Expr> kids;
        for (std::size_t i = 0; i < childCount(e); ++i)
            pushSumTerms(*this, expand(child(e, i)), kids);
        return add(kids);
    }
    case NodeKind::Mul: {
        // Multiply out the sum-views of the expanded factors.
        std::vector<Expr> terms{one()};
        for (std::size_t i = 0; i < childCount(e); ++i) {
            std::vector<Expr> factors;
            pushSumTerms(*this, expand(child(e, i)), factors);
            std::vector<Expr> next;
            next.reserve(terms.size() * factors.size());
            for (const Expr &t : terms)
                for (const Expr &f : factors)
                    next.push_back(mul({t, f}));
            terms = std::move(next);
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
    case NodeKind::Func:
        return func(funcName(e), subs(child(e, 0), from, to));
    case NodeKind::Pow:
        return pow(subs(child(e, 0), from, to),
                   subs(child(e, 1), from, to));
    case NodeKind::Add:
    case NodeKind::Mul: {
        std::vector<Expr> kids;
        kids.reserve(childCount(e));
        for (std::size_t i = 0; i < childCount(e); ++i)
            kids.push_back(subs(child(e, i), from, to));
        return kind(e) == NodeKind::Add ? add(kids) : mul(kids);
    }
    }
    return e;
}

std::string Ctx::toString(Expr e) const
{
    std::string out;
    print(e, out);
    return out;
}

} // namespace numkit::cas
