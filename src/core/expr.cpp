#include <numkit/cas/core/expr.hpp>
#include <numkit/cas/poly/sturm.hpp>

#include <algorithm>
#include <cmath>

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

Expr Ctx::func(const std::string &name, Expr arg0, Expr arg1)
{
    const std::uint32_t id = internName(name, funcIds_, funcNames_);
    return makeNode(NodeKind::Func, id, {arg0, arg1}, Rational(std::int64_t{0}));
}

Expr Ctx::func(const std::string &name, const std::vector<Expr> &args)
{
    const std::uint32_t id = internName(name, funcIds_, funcNames_);
    return makeNode(NodeKind::Func, id, args, Rational(std::int64_t{0}));
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
        const std::size_t n = std::min(na.childCount, nb.childCount);
        for (std::size_t i = 0; i < n; ++i) {
            const int c = compare(child(a, i), child(b, i));
            if (c != 0)
                return c;
        }
        return na.childCount < nb.childCount ? -1
               : na.childCount > nb.childCount ? 1 : 0;
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
        for (std::size_t i = 0; i < n.childCount; ++i) {
            if (i > 0)
                out += ", ";
            printPrec(child(e, i), out, 0);
        }
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

namespace {

bool bernoulliExact(std::int64_t n, Rational &out)
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
    std::vector<Rational> a(static_cast<std::size_t>(n + 1));
    for (std::int64_t m = 0; m <= n; ++m) {
        a[static_cast<std::size_t>(m)] = Rational(1, BigInt(m + 1));
        for (std::int64_t j = m; j >= 1; --j) {
            const std::size_t idx = static_cast<std::size_t>(j - 1);
            a[idx] = Rational(j) * (a[idx] - a[idx + 1]);
        }
    }
    out = a[0];
    return true;
}

bool eulerExact(std::int64_t n, Rational &out)
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
    const std::int64_t mMax = n / 2;
    std::vector<BigInt> eEven(static_cast<std::size_t>(mMax + 1), BigInt(0));
    eEven[0] = BigInt(1);
    for (std::int64_t m = 1; m <= mMax; ++m) {
        BigInt sum(0);
        BigInt binom(1);
        for (std::int64_t k = 0; k < m; ++k) {
            if (k > 0) {
                binom = (binom * BigInt(2 * m - 2 * k + 2) *
                         BigInt(2 * m - 2 * k + 1)) /
                        (BigInt(2 * k - 1) * BigInt(2 * k));
            }
            sum = sum + binom * eEven[static_cast<std::size_t>(k)];
        }
        eEven[static_cast<std::size_t>(m)] = -sum;
    }
    out = Rational(eEven[static_cast<std::size_t>(mMax)], BigInt(1));
    return true;
}

bool evalBernoulliPolyExact(std::int64_t n, const Rational &x, Rational &out)
{
    if (n < 0 || n > 40)
        return false;
    Rational sum(0);
    BigInt binom(1);
    for (std::int64_t k = 0; k <= n; ++k) {
        if (k > 0)
            binom = (binom * BigInt(n - k + 1)) / BigInt(k);
        Rational bk;
        if (!bernoulliExact(k, bk))
            return false;
        if (!bk.isZero()) {
            sum = sum + Rational(binom, BigInt(1)) * bk *
                            Rational::powUInt(
                                x, static_cast<std::uint64_t>(n - k));
        }
    }
    out = sum;
    return true;
}

bool evalEulerPolyExact(std::int64_t n, const Rational &x, Rational &out)
{
    if (n < 0 || n > 40)
        return false;
    const Rational xShift = x - Rational(1, BigInt(2));
    Rational sum(0);
    BigInt binom(1);
    for (std::int64_t k = 0; k <= n; ++k) {
        if (k > 0)
            binom = (binom * BigInt(n - k + 1)) / BigInt(k);
        Rational ek;
        if (!eulerExact(k, ek))
            return false;
        if (!ek.isZero()) {
            const BigInt twoPow =
                BigInt::powUInt(BigInt(2), static_cast<std::size_t>(k));
            sum = sum + Rational(binom, twoPow) * ek *
                            Rational::powUInt(
                                xShift, static_cast<std::uint64_t>(n - k));
        }
    }
    out = sum;
    return true;
}

bool evalPolylogNegIntExact(std::int64_t m, const Rational &z, Rational &out)
{
    if (m < 0 || m > 20 || z == Rational(1))
        return false;
    const Rational den =
        Rational::powUInt(Rational(1) - z, static_cast<std::uint64_t>(m + 1));
    if (m == 0) {
        out = z / den;
        return true;
    }
    std::vector<BigInt> eul(static_cast<std::size_t>(m), BigInt(0));
    eul[0] = BigInt(1);
    for (std::int64_t i = 2; i <= m; ++i) {
        for (std::int64_t k = i - 1; k >= 1; --k) {
            eul[static_cast<std::size_t>(k)] =
                BigInt(k + 1) * eul[static_cast<std::size_t>(k)] +
                BigInt(i - k) * eul[static_cast<std::size_t>(k - 1)];
        }
    }
    Rational num(0);
    for (std::int64_t k = 0; k < m; ++k) {
        num = num + Rational(eul[static_cast<std::size_t>(k)], BigInt(1)) *
                        Rational::powUInt(z, static_cast<std::uint64_t>(m - k));
    }
    out = num / den;
    return true;
}

} // namespace

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
        const std::string &name = funcName(e);
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
            std::int64_t mTerm = -1;
            if (aVal.den() == BigInt(1) && aVal.signum() <= 0) {
                std::int64_t ma = 0;
                if (aVal.num().fitsInt64(ma) && -ma <= 40)
                    mTerm = -ma;
            }
            if (bVal.den() == BigInt(1) && bVal.signum() <= 0) {
                std::int64_t mb = 0;
                if (bVal.num().fitsInt64(mb) && -mb <= 40 &&
                    (mTerm < 0 || -mb < mTerm)) {
                    mTerm = -mb;
                }
            }
            if (mTerm >= 0) {
                Rational sum = one, term = one;
                for (std::int64_t k = 0; k < mTerm; ++k) {
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
            std::int64_t ma = 0;
            if (aVal.den() == BigInt(1) && aVal.signum() <= 0 &&
                aVal.num().fitsInt64(ma) && -ma <= 40) {
                const std::int64_t mTerm = -ma;
                Rational sum = one, term = one;
                for (std::int64_t k = 0; k < mTerm; ++k) {
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
                std::int64_t nInt = 0;
                if (nVal.num().fitsInt64(nInt) && nInt >= 1 && nInt <= 30) {
                    BigInt fact(1);
                    for (std::int64_t k = 2; k < nInt; ++k)
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
                std::int64_t kCount = 0;
                if (xVal.num().fitsInt64(kCount) && kCount >= 0 &&
                    kCount <= 40) {
                    Rational prod = one;
                    for (std::int64_t j = 0; j < kCount; ++j)
                        prod = prod * (nVal + Rational(j));
                    out = prod;
                    return true;
                }
                return false;
            }
            if ((name == "stirlingS1" || name == "stirlingS2") && hasX &&
                nVal.den() == BigInt(1) && xVal.den() == BigInt(1)) {
                std::int64_t nInt = 0, kInt = 0;
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
                    std::vector<BigInt> row(static_cast<std::size_t>(kInt + 1),
                                            BigInt(0));
                    row[0] = BigInt(1);
                    for (std::int64_t i = 1; i <= nInt; ++i) {
                        const std::int64_t jMax = std::min(i, kInt);
                        for (std::int64_t j = jMax; j >= 1; --j) {
                            const auto ju = static_cast<std::size_t>(j);
                            if (name == "stirlingS1") {
                                row[ju] = row[ju - 1] - BigInt(i - 1) * row[ju];
                            } else {
                                row[ju] = BigInt(j) * row[ju] + row[ju - 1];
                            }
                        }
                        row[0] = BigInt(0);
                    }
                    out = Rational(row[static_cast<std::size_t>(kInt)], BigInt(1));
                    return true;
                }
                return false;
            }
            if (name == "beta" && hasX && nVal.den() == BigInt(1) &&
                xVal.den() == BigInt(1)) {
                std::int64_t mInt = 0, kInt = 0;
                if (nVal.num().fitsInt64(mInt) && xVal.num().fitsInt64(kInt) &&
                    mInt >= 1 && kInt >= 1 && mInt + kInt <= 50) {
                    BigInt fM(1), fK(1), fMK(1);
                    for (std::int64_t j = 2; j < mInt; ++j)
                        fM = fM * BigInt(j);
                    for (std::int64_t j = 2; j < kInt; ++j)
                        fK = fK * BigInt(j);
                    for (std::int64_t j = 2; j < mInt + kInt; ++j)
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
            std::int64_t n = 0;
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
                for (std::int64_t k = 1; k < n; ++k) {
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
                for (std::int64_t k = 1; k < n; ++k) {
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
                for (std::int64_t k = 1; k < n; ++k) {
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
                for (std::int64_t k = 1; k < n; ++k) {
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
                for (std::int64_t k = 1; k < n; ++k) {
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
            std::int64_t k = 0;
            if (a.num().fitsInt64(k))
                return bernoulliExact(k, out);
            return false;
        }
        if (name == "eulerE" && a.den() == BigInt(1)) {
            std::int64_t k = 0;
            if (a.num().fitsInt64(k))
                return eulerExact(k, out);
            return false;
        }
        if (name == "zeta" && a.den() == BigInt(1)) {
            std::int64_t s = 0;
            if (a.num().fitsInt64(s) && s <= 0 && s >= -59) {
                if (s == 0) {
                    out = Rational(-1, BigInt(2));
                    return true;
                }
                const std::int64_t m = -s;
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
            std::int64_t s = 0;
            if (a.num().fitsInt64(s) && s <= 0 && s >= -59) {
                if (s == 0) {
                    out = Rational(1, BigInt(2));
                    return true;
                }
                const std::int64_t m = -s;
                Rational bVal;
                if (!bernoulliExact(m + 1, bVal))
                    return false;
                const BigInt twoPow =
                    BigInt::powUInt(BigInt(2), static_cast<std::size_t>(m + 1));
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
            std::int64_t k = 0;
            if (a.num().fitsInt64(k) && k >= 0 && k <= 30) {
                BigInt fact(1);
                for (std::int64_t i = 2; i <= k; ++i)
                    fact = fact * BigInt(i);
                out = Rational(fact, BigInt(1));
                return true;
            }
        }
        if (name == "gamma" && a.den() == BigInt(1)) {
            std::int64_t k = 0;
            if (a.num().fitsInt64(k) && k >= 1 && k <= 31) {
                BigInt fact(1);
                for (std::int64_t i = 2; i <= k - 1; ++i)
                    fact = fact * BigInt(i);
                out = Rational(fact, BigInt(1));
                return true;
            }
        }
        if ((name == "lgamma" || name == "loggamma") &&
            (a == one || a == Rational(std::int64_t{2}))) {
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

constexpr double kPiDouble = 3.141592653589793238462643383279502884;
constexpr double kEulerGamma = 0.577215664901532860606512090082402431;

double evalErfiDouble(double x)
{
    if (x == 0.0)
        return 0.0;
    const double sgn = x < 0.0 ? -1.0 : 1.0;
    const double ax = std::abs(x);
    if (ax > 26.5)
        return sgn * HUGE_VAL;
    const double x2 = ax * ax;
    double term = ax;
    double sum = term;
    for (int n = 1; n <= 200; ++n) {
        term *= x2 / static_cast<double>(n);
        const double contrib = term / static_cast<double>(2 * n + 1);
        sum += contrib;
        if (contrib <= sum * 1e-16)
            break;
    }
    return sgn * (2.0 / std::sqrt(kPiDouble)) * sum;
}

bool evalEiDouble(double x, double &out)
{
    if (x == 0.0)
        return false;
    if (x > 0.0) {
        if (x > 700.0)
            return false;
        double sum = 0.0;
        double term = 1.0;
        for (int n = 1; n <= 300; ++n) {
            term *= x / static_cast<double>(n);
            const double contrib = term / static_cast<double>(n);
            sum += contrib;
            if (contrib <= sum * 1e-16 && n > x)
                break;
        }
        out = kEulerGamma + std::log(x) + sum;
        return std::isfinite(out);
    }
    const double z = -x;
    if (z <= 4.0) {
        double sum = 0.0;
        double term = 1.0;
        for (int n = 1; n <= 120; ++n) {
            term *= x / static_cast<double>(n);
            const double contrib = term / static_cast<double>(n);
            sum += contrib;
            if (std::abs(contrib) <= 1e-16)
                break;
        }
        out = kEulerGamma + std::log(z) + sum;
        return std::isfinite(out);
    }
    // Continued fraction for E_1(z) (z > 4):
    // E_1(z) = exp(-z) / (z + 1/(1 + 1/(z + 2/(1 + 2/(z + ...)))))
    double b = z + 1.0;
    double c = 1.0 / 1e-30;
    double d = 1.0 / b;
    double h = d;
    for (int i = 1; i <= 100; ++i) {
        const double a = -static_cast<double>(i * i);
        b += 2.0;
        d = a * d + b;
        if (std::abs(d) < 1e-30)
            d = 1e-30;
        c = b + a / c;
        if (std::abs(c) < 1e-30)
            c = 1e-30;
        d = 1.0 / d;
        const double del = d * c;
        h *= del;
        if (std::abs(del - 1.0) <= 1e-16)
            break;
    }
    out = -std::exp(-z) * h;
    return std::isfinite(out);
}

// 8-point Gauss-Legendre quadrature on [a, b].
template <typename Fn>
double gauss8Integrate(Fn &&fn, double a, double b, int panels)
{
    static constexpr double kNodes[4] = {
        0.183434642495649805, 0.525532409916328986,
        0.796666477413626740, 0.960289856497536232};
    static constexpr double kWeights[4] = {
        0.362683783378361983, 0.313706645877887287,
        0.222381034453374471, 0.101228536290376259};
    const double h = (b - a) / static_cast<double>(panels);
    double total = 0.0;
    for (int p = 0; p < panels; ++p) {
        const double x0 = a + p * h;
        const double mid = x0 + 0.5 * h;
        const double half = 0.5 * h;
        double sub = 0.0;
        for (int i = 0; i < 4; ++i) {
            const double dx = half * kNodes[i];
            sub += kWeights[i] * (fn(mid - dx) + fn(mid + dx));
        }
        total += half * sub;
    }
    return total;
}

double evalSiDouble(double x)
{
    if (x == 0.0)
        return 0.0;
    const double sgn = x < 0.0 ? -1.0 : 1.0;
    const double ax = std::abs(x);
    if (ax <= 4.0) {
        const double x2 = ax * ax;
        double term = ax;
        double sum = term;
        for (int n = 1; n <= 50; ++n) {
            term *= -x2 / static_cast<double>((2 * n) * (2 * n + 1));
            const double contrib = term / static_cast<double>(2 * n + 1);
            sum += contrib;
            if (std::abs(contrib) <= 1e-16)
                break;
        }
        return sgn * sum;
    }
    if (ax <= 32.0) {
        const double si4 = evalSiDouble(4.0);
        const int panels = std::max(8, static_cast<int>(std::ceil((ax - 4.0) * 2.0)));
        const double tail = gauss8Integrate(
            [](double t) { return std::sin(t) / t; }, 4.0, ax, panels);
        return sgn * (si4 + tail);
    }
    // Asymptotic expansion via f(z), g(z) for z > 32.
    const double invZ2 = 1.0 / (ax * ax);
    double fSum = 1.0, gSum = 1.0;
    double fTerm = 1.0, gTerm = 1.0;
    for (int k = 1; k <= 12; ++k) {
        fTerm *= -static_cast<double>((2 * k - 1) * (2 * k)) * invZ2;
        if (std::abs(fTerm) > 1e-3 && k > 4)
            break;
        fSum += fTerm;
        gTerm *= -static_cast<double>((2 * k) * (2 * k + 1)) * invZ2;
        gSum += gTerm;
    }
    const double fVal = fSum / ax;
    const double gVal = gSum * invZ2;
    return sgn * (0.5 * kPiDouble - fVal * std::cos(ax) - gVal * std::sin(ax));
}

bool evalCiDouble(double x, double &out)
{
    if (x <= 0.0)
        return false;
    if (x <= 4.0) {
        const double x2 = x * x;
        double term = 1.0;
        double sum = 0.0;
        for (int n = 1; n <= 50; ++n) {
            term *= -x2 / static_cast<double>((2 * n - 1) * (2 * n));
            const double contrib = term / static_cast<double>(2 * n);
            sum += contrib;
            if (std::abs(contrib) <= 1e-16)
                break;
        }
        out = kEulerGamma + std::log(x) + sum;
        return std::isfinite(out);
    }
    if (x <= 32.0) {
        double ci4 = 0.0;
        evalCiDouble(4.0, ci4);
        const int panels = std::max(8, static_cast<int>(std::ceil((x - 4.0) * 2.0)));
        const double tail = gauss8Integrate(
            [](double t) { return std::cos(t) / t; }, 4.0, x, panels);
        out = ci4 + tail;
        return std::isfinite(out);
    }
    const double invZ2 = 1.0 / (x * x);
    double fSum = 1.0, gSum = 1.0;
    double fTerm = 1.0, gTerm = 1.0;
    for (int k = 1; k <= 12; ++k) {
        fTerm *= -static_cast<double>((2 * k - 1) * (2 * k)) * invZ2;
        if (std::abs(fTerm) > 1e-3 && k > 4)
            break;
        fSum += fTerm;
        gTerm *= -static_cast<double>((2 * k) * (2 * k + 1)) * invZ2;
        gSum += gTerm;
    }
    const double fVal = fSum / x;
    const double gVal = gSum * invZ2;
    out = fVal * std::sin(x) - gVal * std::cos(x);
    return std::isfinite(out);
}

double evalFresnelDouble(double x, bool isSine)
{
    if (x == 0.0)
        return 0.0;
    const double sgn = x < 0.0 ? -1.0 : 1.0;
    const double ax = std::abs(x);
    if (ax <= 2.5) {
        const double halfPi = 0.5 * kPiDouble;
        const double x2 = ax * ax;
        const double x4 = x2 * x2;
        if (isSine) {
            double term = halfPi * ax * x2;
            double sum = term / 3.0;
            for (int n = 1; n <= 45; ++n) {
                term *= -(halfPi * halfPi * x4) /
                        static_cast<double>((2 * n) * (2 * n + 1));
                const double contrib = term / static_cast<double>(4 * n + 3);
                sum += contrib;
                if (std::abs(contrib) <= 1e-16)
                    break;
            }
            return sgn * sum;
        }
        double term = ax;
        double sum = term;
        for (int n = 1; n <= 45; ++n) {
            term *= -(halfPi * halfPi * x4) /
                    static_cast<double>((2 * n - 1) * (2 * n));
            const double contrib = term / static_cast<double>(4 * n + 1);
            sum += contrib;
            if (std::abs(contrib) <= 1e-16)
                break;
        }
        return sgn * sum;
    }
    if (ax <= 12.0) {
        const double base = evalFresnelDouble(2.5, isSine);
        const int panels = std::max(16, static_cast<int>(std::ceil((ax * ax - 6.25) * 4.0)));
        const double tail = gauss8Integrate(
            [isSine](double t) {
                const double arg = 0.5 * kPiDouble * t * t;
                return isSine ? std::sin(arg) : std::cos(arg);
            },
            2.5, ax, panels);
        return sgn * (base + tail);
    }
    // Asymptotic expansion for ax > 12.
    const double z = 0.5 * kPiDouble * ax * ax;
    const double invPiAx = 1.0 / (kPiDouble * ax);
    const double inv2Z = 1.0 / (2.0 * z);
    const double fVal = invPiAx * (1.0 - 3.0 * inv2Z * inv2Z);
    const double gVal = invPiAx * inv2Z * (1.0 - 15.0 * inv2Z * inv2Z);
    if (isSine)
        return sgn * (0.5 - fVal * std::cos(z) - gVal * std::sin(z));
    return sgn * (0.5 + fVal * std::sin(z) - gVal * std::cos(z));
}

bool evalDilogDouble(double x, double &out)
{
    if (!std::isfinite(x) || x > 1.0)
        return false;
    if (x == 0.0) {
        out = 0.0;
        return true;
    }
    const double pi2Over6 = (kPiDouble * kPiDouble) / 6.0;
    if (x == 1.0) {
        out = pi2Over6;
        return true;
    }
    if (x == -1.0) {
        out = -0.5 * pi2Over6;
        return true;
    }
    if (x < -1.0) {
        double sub = 0.0;
        if (!evalDilogDouble(1.0 / x, sub))
            return false;
        const double lnx = std::log(-x);
        out = -sub - pi2Over6 - 0.5 * lnx * lnx;
        return std::isfinite(out);
    }
    if (x < -0.5) {
        double sub = 0.0;
        if (!evalDilogDouble(x / (x - 1.0), sub))
            return false;
        const double ln1mx = std::log(1.0 - x);
        out = -sub - 0.5 * ln1mx * ln1mx;
        return std::isfinite(out);
    }
    if (x > 0.5) {
        double sub = 0.0;
        if (!evalDilogDouble(1.0 - x, sub))
            return false;
        out = pi2Over6 - std::log(x) * std::log(1.0 - x) - sub;
        return std::isfinite(out);
    }
    double sum = 0.0;
    double xPow = x;
    for (int k = 1; k <= 60; ++k) {
        const double kd = static_cast<double>(k);
        const double contrib = xPow / (kd * kd);
        sum += contrib;
        if (std::abs(contrib) <= 1e-16 * std::abs(sum))
            break;
        xPow *= x;
    }
    out = sum;
    return std::isfinite(out);
}

bool evalDigammaDouble(double x, double &out)
{
    if (!std::isfinite(x))
        return false;
    if (x <= 0.0) {
        if (std::floor(x) == x)
            return false;
        double sub = 0.0;
        if (!evalDigammaDouble(1.0 - x, sub))
            return false;
        const double r = x - std::floor(x);
        const double s = std::sin(kPiDouble * r);
        if (s == 0.0)
            return false;
        out = sub - kPiDouble * (std::cos(kPiDouble * r) / s);
        return std::isfinite(out);
    }
    double shift = 0.0;
    while (x < 10.0) {
        shift -= 1.0 / x;
        x += 1.0;
    }
    const double invX = 1.0 / x;
    const double invX2 = invX * invX;
    // psi(x) ~ ln(x) - 1/(2x) - sum_{k=1}^7 B_{2k}/(2k * x^{2k})
    const double poly =
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
    out = shift + std::log(x) - 0.5 * invX - invX2 * poly;
    return std::isfinite(out);
}

bool evalTrigammaDouble(double x, double &out)
{
    if (!std::isfinite(x))
        return false;
    if (x <= 0.0) {
        if (std::floor(x) == x)
            return false;
        double sub = 0.0;
        if (!evalTrigammaDouble(1.0 - x, sub))
            return false;
        const double r = x - std::floor(x);
        const double s = std::sin(kPiDouble * r);
        if (s == 0.0)
            return false;
        out = (kPiDouble * kPiDouble) / (s * s) - sub;
        return std::isfinite(out);
    }
    double shift = 0.0;
    while (x < 10.0) {
        shift += 1.0 / (x * x);
        x += 1.0;
    }
    const double invX = 1.0 / x;
    const double invX2 = invX * invX;
    // psi_1(x) ~ 1/x + 1/(2x^2) + sum_{k=1}^6 B_{2k}/x^{2k+1}
    const double poly =
        (1.0 / 6.0) +
        invX2 *
            ((-1.0 / 30.0) +
             invX2 *
                 ((1.0 / 42.0) +
                  invX2 *
                      ((-1.0 / 30.0) +
                       invX2 * ((5.0 / 66.0) + invX2 * (-691.0 / 2730.0)))));
    out = shift + invX + 0.5 * invX2 + (invX * invX2) * poly;
    return std::isfinite(out);
}

bool evalBesselJDouble(double nu, double x, double &out)
{
    if (!std::isfinite(nu) || !std::isfinite(x))
        return false;
    const bool isIntNu = (std::floor(nu) == nu);
    if (x == 0.0) {
        if (nu == 0.0) { out = 1.0; return true; }
        if (nu > 0.0) { out = 0.0; return true; }
        return false;
    }
    double signFactor = 1.0;
    if (isIntNu && nu < 0.0) {
        const long long nInt = static_cast<long long>(-nu);
        if (nInt % 2 != 0)
            signFactor = -signFactor;
        nu = -nu;
    }
    if (x < 0.0) {
        if (!isIntNu)
            return false;
        const long long nInt = static_cast<long long>( std::abs(nu) );
        if (nInt % 2 != 0)
            signFactor = -signFactor;
        x = -x;
    }
    if (x <= 12.0 + 0.5 * std::abs(nu)) {
        const double halfX = 0.5 * x;
        const double halfX2 = halfX * halfX;
        double sum = 0.0;
        if (nu >= 0.0) {
            double term = std::exp(nu * std::log(halfX) - std::lgamma(nu + 1.0));
            sum = term;
            for (int k = 1; k <= 160; ++k) {
                term *= -halfX2 / (static_cast<double>(k) * (nu + static_cast<double>(k)));
                sum += term;
                if (std::abs(term) <= std::abs(sum) * 1e-16 && k > halfX)
                    break;
            }
        } else {
            for (int k = 0; k <= 160; ++k) {
                const double gArg = nu + static_cast<double>(k) + 1.0;
                const double gam = std::tgamma(gArg);
                if (!std::isfinite(gam) || gam == 0.0)
                    continue;
                double kFact = std::tgamma(static_cast<double>(k) + 1.0);
                double term = ((k % 2 == 0) ? 1.0 : -1.0) *
                              std::pow(halfX, 2.0 * k + nu) / (kFact * gam);
                sum += term;
                if (k > 10 && std::abs(term) <= std::abs(sum) * 1e-16 && k > halfX)
                    break;
            }
        }
        out = signFactor * sum;
        return std::isfinite(out);
    }
    // Hankel asymptotic expansion for x > 12 + 0.5*|nu|
    const double mu = 4.0 * nu * nu;
    const double chi = x - (0.5 * nu + 0.25) * kPiDouble;
    double P = 1.0, Q = 0.0;
    double aTerm = 1.0;
    for (int m = 1; m <= 24; ++m) {
        const double num = mu - static_cast<double>((2 * m - 1) * (2 * m - 1));
        const double nextA = aTerm * num / (static_cast<double>(m) * 8.0 * x);
        if (m > 4 && std::abs(nextA) > std::abs(aTerm))
            break;
        aTerm = nextA;
        if (m % 2 == 1) {
            const double sgn = ((m / 2) % 2 == 0) ? 1.0 : -1.0;
            Q += sgn * aTerm;
        } else {
            const double sgn = ((m / 2) % 2 == 0) ? 1.0 : -1.0;
            P += sgn * aTerm;
        }
        if (std::abs(aTerm) < 1e-16)
            break;
    }
    out = signFactor * std::sqrt(2.0 / (kPiDouble * x)) *
          (P * std::cos(chi) - Q * std::sin(chi));
    return std::isfinite(out);
}

bool evalBesselYDouble(double nu, double x, double &out)
{
    if (!std::isfinite(nu) || !std::isfinite(x) || x <= 0.0)
        return false;
    if (x > 12.0 + 0.5 * std::abs(nu)) {
        const double mu = 4.0 * nu * nu;
        const double chi = x - (0.5 * nu + 0.25) * kPiDouble;
        double P = 1.0, Q = 0.0;
        double aTerm = 1.0;
        for (int m = 1; m <= 24; ++m) {
            const double num = mu - static_cast<double>((2 * m - 1) * (2 * m - 1));
            const double nextA = aTerm * num / (static_cast<double>(m) * 8.0 * x);
            if (m > 4 && std::abs(nextA) > std::abs(aTerm))
                break;
            aTerm = nextA;
            if (m % 2 == 1) {
                const double sgn = ((m / 2) % 2 == 0) ? 1.0 : -1.0;
                Q += sgn * aTerm;
            } else {
                const double sgn = ((m / 2) % 2 == 0) ? 1.0 : -1.0;
                P += sgn * aTerm;
            }
            if (std::abs(aTerm) < 1e-16)
                break;
        }
        out = std::sqrt(2.0 / (kPiDouble * x)) *
              (P * std::sin(chi) + Q * std::cos(chi));
        return std::isfinite(out);
    }
    if (std::floor(nu) != nu) {
        double jPos = 0.0, jNeg = 0.0;
        if (!evalBesselJDouble(nu, x, jPos) || !evalBesselJDouble(-nu, x, jNeg))
            return false;
        out = (jPos * std::cos(nu * kPiDouble) - jNeg) / std::sin(nu * kPiDouble);
        return std::isfinite(out);
    }
    double signFactor = 1.0;
    int n = static_cast<int>(nu);
    if (n < 0) {
        n = -n;
        if (n % 2 != 0)
            signFactor = -1.0;
    }
    if (n > 30)
        return false;
    double jn = 0.0;
    if (!evalBesselJDouble(static_cast<double>(n), x, jn))
        return false;
    const double halfX = 0.5 * x;
    const double halfX2 = halfX * halfX;
    double poleSum = 0.0;
    for (int k = 0; k < n; ++k) {
        const double numFact = std::tgamma(static_cast<double>(n - k));
        const double denFact = std::tgamma(static_cast<double>(k + 1));
        poleSum += (numFact / denFact) * std::pow(halfX, 2 * k - n);
    }
    double hN = 0.0;
    for (int j = 1; j <= n; ++j)
        hN += 1.0 / static_cast<double>(j);
    double hK = 0.0;
    double powTerm = std::pow(halfX, n) / std::tgamma(static_cast<double>(n + 1));
    double regSum = (hK + hN) * powTerm;
    for (int k = 1; k <= 120; ++k) {
        hK += 1.0 / static_cast<double>(k);
        hN += 1.0 / static_cast<double>(n + k);
        powTerm *= -halfX2 / (static_cast<double>(k) * static_cast<double>(n + k));
        const double contrib = (hK + hN) * powTerm;
        regSum += contrib;
        if (std::abs(contrib) <= std::abs(regSum) * 1e-16 && k > halfX)
            break;
    }
    out = signFactor *
          ((2.0 / kPiDouble) * (std::log(halfX) + kEulerGamma) * jn -
           (poleSum + regSum) / kPiDouble);
    return std::isfinite(out);
}

bool evalBesselIDouble(double nu, double x, double &out)
{
    if (!std::isfinite(nu) || !std::isfinite(x))
        return false;
    const bool isIntNu = (std::floor(nu) == nu);
    if (x == 0.0) {
        if (nu == 0.0) { out = 1.0; return true; }
        if (nu > 0.0) { out = 0.0; return true; }
        return false;
    }
    if (isIntNu && nu < 0.0)
        nu = -nu;
    double signFactor = 1.0;
    if (x < 0.0) {
        if (!isIntNu)
            return false;
        const long long nInt = static_cast<long long>(std::abs(nu));
        if (nInt % 2 != 0)
            signFactor = -1.0;
        x = -x;
    }
    if (x <= 14.0 + 0.5 * std::abs(nu)) {
        const double halfX = 0.5 * x;
        const double halfX2 = halfX * halfX;
        double sum = 0.0;
        if (nu >= 0.0) {
            double term = std::exp(nu * std::log(halfX) - std::lgamma(nu + 1.0));
            sum = term;
            for (int k = 1; k <= 160; ++k) {
                term *= halfX2 / (static_cast<double>(k) * (nu + static_cast<double>(k)));
                sum += term;
                if (std::abs(term) <= std::abs(sum) * 1e-16 && k > halfX)
                    break;
            }
        } else {
            for (int k = 0; k <= 160; ++k) {
                const double gArg = nu + static_cast<double>(k) + 1.0;
                const double gam = std::tgamma(gArg);
                if (!std::isfinite(gam) || gam == 0.0)
                    continue;
                const double kFact = std::tgamma(static_cast<double>(k) + 1.0);
                const double term = std::pow(halfX, 2.0 * k + nu) / (kFact * gam);
                sum += term;
                if (k > 10 && std::abs(term) <= std::abs(sum) * 1e-16 && k > halfX)
                    break;
            }
        }
        out = signFactor * sum;
        return std::isfinite(out);
    }
    const double mu = 4.0 * nu * nu;
    double sum = 1.0, term = 1.0;
    for (int k = 1; k <= 24; ++k) {
        const double num = mu - static_cast<double>((2 * k - 1) * (2 * k - 1));
        const double next = -term * num / (static_cast<double>(k) * 8.0 * x);
        if (k > 4 && std::abs(next) > std::abs(term))
            break;
        term = next;
        sum += term;
        if (std::abs(term) < 1e-16)
            break;
    }
    out = signFactor * (std::exp(x) / std::sqrt(2.0 * kPiDouble * x)) * sum;
    return std::isfinite(out);
}

bool evalBesselKDouble(double nu, double x, double &out)
{
    if (!std::isfinite(nu) || !std::isfinite(x) || x <= 0.0)
        return false;
    nu = std::abs(nu);
    if (x > 9.0 + 0.5 * nu) {
        const double mu = 4.0 * nu * nu;
        double sum = 1.0, term = 1.0;
        for (int k = 1; k <= 24; ++k) {
            const double num = mu - static_cast<double>((2 * k - 1) * (2 * k - 1));
            const double next = term * num / (static_cast<double>(k) * 8.0 * x);
            if (k > 4 && std::abs(next) > std::abs(term))
                break;
            term = next;
            sum += term;
            if (std::abs(term) < 1e-16)
                break;
        }
        out = std::sqrt(kPiDouble / (2.0 * x)) * std::exp(-x) * sum;
        return std::isfinite(out);
    }
    if (std::floor(nu) != nu) {
        double iPos = 0.0, iNeg = 0.0;
        if (!evalBesselIDouble(nu, x, iPos) || !evalBesselIDouble(-nu, x, iNeg))
            return false;
        out = (0.5 * kPiDouble) * (iNeg - iPos) / std::sin(nu * kPiDouble);
        return std::isfinite(out);
    }
    const int n = static_cast<int>(nu);
    if (n > 30)
        return false;
    double inVal = 0.0;
    if (!evalBesselIDouble(static_cast<double>(n), x, inVal))
        return false;
    const double halfX = 0.5 * x;
    const double halfX2 = halfX * halfX;
    double poleSum = 0.0;
    for (int k = 0; k < n; ++k) {
        const double sgn = (k % 2 == 0) ? 1.0 : -1.0;
        const double numFact = std::tgamma(static_cast<double>(n - k));
        const double denFact = std::tgamma(static_cast<double>(k + 1));
        poleSum += sgn * (numFact / denFact) * std::pow(halfX, 2 * k - n);
    }
    double hN = 0.0;
    for (int j = 1; j <= n; ++j)
        hN += 1.0 / static_cast<double>(j);
    double hK = 0.0;
    double powTerm = std::pow(halfX, n) / std::tgamma(static_cast<double>(n + 1));
    double regSum = (hK + hN) * powTerm;
    for (int k = 1; k <= 120; ++k) {
        hK += 1.0 / static_cast<double>(k);
        hN += 1.0 / static_cast<double>(n + k);
        powTerm *= halfX2 / (static_cast<double>(k) * static_cast<double>(n + k));
        const double contrib = (hK + hN) * powTerm;
        regSum += contrib;
        if (std::abs(contrib) <= std::abs(regSum) * 1e-16 && k > halfX)
            break;
    }
    const double sgnN = (n % 2 == 0) ? 1.0 : -1.0;
    out = -sgnN * (std::log(halfX) + kEulerGamma) * inVal + 0.5 * poleSum +
          0.5 * sgnN * regSum;
    return std::isfinite(out);
}

bool evalAiryDouble(const std::string &fn, double x, double &out)
{
    if (!std::isfinite(x))
        return false;
    static constexpr double kAi0 = 0.35502805388781723926;
    static constexpr double kAiP0 = 0.25881940379280679840;
    const double sqrt3 = std::sqrt(3.0);
    if (std::abs(x) <= 5.5) {
        const double x2 = x * x;
        const double x3 = x2 * x;
        double f = 1.0, fp = 0.0, cTerm = 1.0;
        double g = x, gp = 1.0, dTerm = 1.0;
        for (int k = 1; k <= 60; ++k) {
            cTerm *= x3 / static_cast<double>((3 * k - 1) * (3 * k));
            f += cTerm;
            fp += static_cast<double>(3 * k) * (cTerm / x);
            dTerm *= x3 / static_cast<double>((3 * k) * (3 * k + 1));
            g += dTerm * x;
            gp += static_cast<double>(3 * k + 1) * dTerm;
            if (std::abs(cTerm) <= 1e-16 && std::abs(dTerm) <= 1e-16)
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
        return std::isfinite(out);
    }
    const double ax = std::abs(x);
    const double zeta = (2.0 / 3.0) * ax * std::sqrt(ax);
    if (x > 0.0) {
        if (fn == "airyAi") {
            double kVal = 0.0;
            if (!evalBesselKDouble(1.0 / 3.0, zeta, kVal))
                return false;
            out = (1.0 / kPiDouble) * std::sqrt(x / 3.0) * kVal;
            return std::isfinite(out);
        }
        if (fn == "airyAiPrime") {
            double kVal = 0.0;
            if (!evalBesselKDouble(2.0 / 3.0, zeta, kVal))
                return false;
            out = -(x / (kPiDouble * sqrt3)) * kVal;
            return std::isfinite(out);
        }
        if (fn == "airyBi") {
            double iPos = 0.0, iNeg = 0.0;
            if (!evalBesselIDouble(1.0 / 3.0, zeta, iPos) ||
                !evalBesselIDouble(-1.0 / 3.0, zeta, iNeg))
                return false;
            out = std::sqrt(x / 3.0) * (iNeg + iPos);
            return std::isfinite(out);
        }
        if (fn == "airyBiPrime") {
            double iPos = 0.0, iNeg = 0.0;
            if (!evalBesselIDouble(2.0 / 3.0, zeta, iPos) ||
                !evalBesselIDouble(-2.0 / 3.0, zeta, iNeg))
                return false;
            out = (x / sqrt3) * (iNeg + iPos);
            return std::isfinite(out);
        }
        return false;
    }
    // x < -5.5
    double j13 = 0.0, jm13 = 0.0, j23 = 0.0, jm23 = 0.0;
    if (fn == "airyAi" || fn == "airyBi") {
        if (!evalBesselJDouble(1.0 / 3.0, zeta, j13) ||
            !evalBesselJDouble(-1.0 / 3.0, zeta, jm13))
            return false;
        out = (fn == "airyAi") ? (std::sqrt(ax) / 3.0) * (j13 + jm13)
                               : std::sqrt(ax / 3.0) * (jm13 - j13);
        return std::isfinite(out);
    }
    if (fn == "airyAiPrime" || fn == "airyBiPrime") {
        if (!evalBesselJDouble(2.0 / 3.0, zeta, j23) ||
            !evalBesselJDouble(-2.0 / 3.0, zeta, jm23))
            return false;
        out = (fn == "airyAiPrime") ? -(ax / 3.0) * (j23 - jm23)
                                    : (ax / sqrt3) * (j23 + jm23);
        return std::isfinite(out);
    }
    return false;
}

bool evalOrthogonalPolyDouble(const std::string &fn, double nVal, double x,
                              double &out)
{
    if (!std::isfinite(nVal) || !std::isfinite(x) || std::floor(nVal) != nVal)
        return false;
    int n = static_cast<int>(nVal);
    if (fn == "legendreP") {
        if (n < 0) n = -n - 1;
        if (n > 200) return false;
        if (n == 0) { out = 1.0; return true; }
        if (n == 1) { out = x; return true; }
        double pPrev = 1.0, pCur = x;
        for (int k = 1; k < n; ++k) {
            const double pNext =
                ((2.0 * k + 1.0) * x * pCur - k * pPrev) / (k + 1.0);
            pPrev = pCur;
            pCur = pNext;
        }
        out = pCur;
        return std::isfinite(out);
    }
    if (fn == "chebyshevT") {
        if (n < 0) n = -n;
        if (n > 200) return false;
        if (n == 0) { out = 1.0; return true; }
        if (n == 1) { out = x; return true; }
        double tPrev = 1.0, tCur = x;
        for (int k = 1; k < n; ++k) {
            const double tNext = 2.0 * x * tCur - tPrev;
            tPrev = tCur;
            tCur = tNext;
        }
        out = tCur;
        return std::isfinite(out);
    }
    if (fn == "chebyshevU") {
        double sgn = 1.0;
        if (n == -1) { out = 0.0; return true; }
        if (n < -1) { n = -n - 2; sgn = -1.0; }
        if (n > 200) return false;
        if (n == 0) { out = sgn; return true; }
        if (n == 1) { out = sgn * 2.0 * x; return true; }
        double uPrev = 1.0, uCur = 2.0 * x;
        for (int k = 1; k < n; ++k) {
            const double uNext = 2.0 * x * uCur - uPrev;
            uPrev = uCur;
            uCur = uNext;
        }
        out = sgn * uCur;
        return std::isfinite(out);
    }
    if (fn == "hermiteH") {
        if (n < 0 || n > 200) return false;
        if (n == 0) { out = 1.0; return true; }
        if (n == 1) { out = 2.0 * x; return true; }
        double hPrev = 1.0, hCur = 2.0 * x;
        for (int k = 1; k < n; ++k) {
            const double hNext = 2.0 * x * hCur - 2.0 * k * hPrev;
            hPrev = hCur;
            hCur = hNext;
        }
        out = hCur;
        return std::isfinite(out);
    }
    if (fn == "laguerreL") {
        if (n < 0 || n > 200) return false;
        if (n == 0) { out = 1.0; return true; }
        if (n == 1) { out = 1.0 - x; return true; }
        double lPrev = 1.0, lCur = 1.0 - x;
        for (int k = 1; k < n; ++k) {
            const double lNext =
                ((2.0 * k + 1.0 - x) * lCur - k * lPrev) / (k + 1.0);
            lPrev = lCur;
            lCur = lNext;
        }
        out = lCur;
        return std::isfinite(out);
    }
    return false;
}

bool carlsonRF(double x, double y, double z, double &out)
{
    if (!std::isfinite(x) || !std::isfinite(y) || !std::isfinite(z) ||
        x < 0.0 || y < 0.0 || z < 0.0)
        return false;
    int zeroCount = (x == 0.0 ? 1 : 0) + (y == 0.0 ? 1 : 0) + (z == 0.0 ? 1 : 0);
    if (zeroCount > 1)
        return false;

    for (int iter = 0; iter < 36; ++iter) {
        const double A = (x + y + z) / 3.0;
        const double dx = std::abs(A - x);
        const double dy = std::abs(A - y);
        const double dz = std::abs(A - z);
        if (std::max({dx, dy, dz}) <= 1e-6 * A)
            break;
        const double sx = std::sqrt(x);
        const double sy = std::sqrt(y);
        const double sz = std::sqrt(z);
        const double lam = sx * sy + sy * sz + sz * sx;
        x = 0.25 * (x + lam);
        y = 0.25 * (y + lam);
        z = 0.25 * (z + lam);
    }
    const double A = (x + y + z) / 3.0;
    if (A <= 0.0)
        return false;
    const double X = (A - x) / A;
    const double Y = (A - y) / A;
    const double Z = -X - Y;
    const double E2 = X * Y - Z * Z;
    const double E3 = X * Y * Z;
    out = (1.0 - (1.0 / 10.0) * E2 + (1.0 / 14.0) * E3 +
           (1.0 / 24.0) * E2 * E2 - (3.0 / 44.0) * E2 * E3) /
          std::sqrt(A);
    return std::isfinite(out);
}

bool carlsonRD(double x, double y, double z, double &out)
{
    if (!std::isfinite(x) || !std::isfinite(y) || !std::isfinite(z) ||
        x < 0.0 || y < 0.0 || z <= 0.0 || (x + y <= 0.0))
        return false;

    double sum = 0.0;
    double fac = 1.0;
    for (int iter = 0; iter < 36; ++iter) {
        const double A = (x + y + 3.0 * z) / 5.0;
        const double dx = std::abs(A - x);
        const double dy = std::abs(A - y);
        const double dz = std::abs(A - z);
        if (std::max({dx, dy, dz}) <= 1e-6 * A)
            break;
        const double sx = std::sqrt(x);
        const double sy = std::sqrt(y);
        const double sz = std::sqrt(z);
        const double lam = sx * sy + sy * sz + sz * sx;
        sum += fac / (sz * (z + lam));
        fac *= 0.25;
        x = 0.25 * (x + lam);
        y = 0.25 * (y + lam);
        z = 0.25 * (z + lam);
    }
    const double A = (x + y + 3.0 * z) / 5.0;
    if (A <= 0.0)
        return false;
    const double X = (A - x) / A;
    const double Y = (A - y) / A;
    const double Z = -(X + Y) / 3.0;
    const double E2 = X * Y - 6.0 * Z * Z;
    const double E3 = (3.0 * X * Y - 8.0 * Z * Z) * Z;
    const double E4 = 3.0 * (X * Y - Z * Z) * Z * Z;
    const double E5 = X * Y * Z * Z * Z;
    const double poly =
        1.0 - (3.0 / 14.0) * E2 + (1.0 / 6.0) * E3 +
        (9.0 / 88.0) * E2 * E2 - (3.0 / 22.0) * E4 -
        (9.0 / 52.0) * E2 * E3 + (3.0 / 26.0) * E5;
    out = 3.0 * sum + fac * poly / (A * std::sqrt(A));
    return std::isfinite(out);
}

bool carlsonRJ(double x, double y, double z, double p, double &out)
{
    if (!std::isfinite(x) || !std::isfinite(y) || !std::isfinite(z) ||
        !std::isfinite(p) || x < 0.0 || y < 0.0 || z < 0.0 || p <= 0.0)
        return false;
    int zeroCount = (x == 0.0 ? 1 : 0) + (y == 0.0 ? 1 : 0) + (z == 0.0 ? 1 : 0);
    if (zeroCount > 1)
        return false;

    double sum = 0.0;
    double fac = 1.0;
    for (int iter = 0; iter < 36; ++iter) {
        const double A = (x + y + z + 2.0 * p) / 5.0;
        const double dx = std::abs(A - x);
        const double dy = std::abs(A - y);
        const double dz = std::abs(A - z);
        const double dp = std::abs(A - p);
        if (std::max({dx, dy, dz, dp}) <= 1e-6 * A)
            break;
        const double sx = std::sqrt(x);
        const double sy = std::sqrt(y);
        const double sz = std::sqrt(z);
        const double sp = std::sqrt(p);
        const double lam = sx * sy + sy * sz + sz * sx;
        const double d = (sp + sx) * (sp + sy) * (sp + sz);
        if (d == 0.0)
            return false;
        const double e = ((p - x) * (p - y) * (p - z)) / (d * d);
        if (e <= -1.0)
            return false;
        double rc = 1.0;
        if (std::abs(e) <= 1e-8) {
            rc = 1.0 - (1.0 / 3.0) * e + (1.0 / 5.0) * e * e -
                 (1.0 / 7.0) * e * e * e;
        } else if (e > 0.0) {
            const double se = std::sqrt(e);
            rc = std::atan(se) / se;
        } else {
            const double sme = std::sqrt(-e);
            rc = std::atanh(sme) / sme;
        }
        sum += fac * rc / d;
        fac *= 0.25;
        x = 0.25 * (x + lam);
        y = 0.25 * (y + lam);
        z = 0.25 * (z + lam);
        p = 0.25 * (p + lam);
    }
    const double A = (x + y + z + 2.0 * p) / 5.0;
    if (A <= 0.0)
        return false;
    const double X = (A - x) / A;
    const double Y = (A - y) / A;
    const double Z = (A - z) / A;
    const double P = -(X + Y + Z) / 2.0;
    const double E2 = X * Y + X * Z + Y * Z - 3.0 * P * P;
    const double E3 = X * Y * Z + 2.0 * E2 * P + 4.0 * P * P * P;
    const double E4 = (2.0 * X * Y * Z + E2 * P + 3.0 * P * P * P) * P;
    const double E5 = X * Y * Z * P * P;
    const double poly =
        1.0 - (3.0 / 14.0) * E2 + (1.0 / 6.0) * E3 +
        (9.0 / 88.0) * E2 * E2 - (3.0 / 22.0) * E4 -
        (9.0 / 52.0) * E2 * E3 + (3.0 / 26.0) * E5;
    out = 6.0 * sum + fac * poly / (A * std::sqrt(A));
    return std::isfinite(out);
}

bool evalElliptic1ArgDouble(const std::string &fn, double m, double &out)
{
    if (!std::isfinite(m) || m > 1.0)
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
        double rf = 0.0, rd = 0.0;
        if (!carlsonRF(0.0, 1.0 - m, 1.0, rf) ||
            !carlsonRD(0.0, 1.0 - m, 1.0, rd))
            return false;
        out = rf - (m / 3.0) * rd;
        return std::isfinite(out);
    }
    return false;
}

bool evalElliptic2ArgDouble(const std::string &fn, double a0, double a1,
                            double &out)
{
    if (!std::isfinite(a0) || !std::isfinite(a1))
        return false;
    if (fn == "ellipticPi") {
        const double n = a0;
        const double m = a1;
        if (m >= 1.0 || n >= 1.0)
            return false;
        double rf = 0.0;
        if (!carlsonRF(0.0, 1.0 - m, 1.0, rf))
            return false;
        if (n == 0.0) {
            out = rf;
            return true;
        }
        double rj = 0.0;
        if (!carlsonRJ(0.0, 1.0 - m, 1.0, 1.0 - n, rj))
            return false;
        out = rf + (n / 3.0) * rj;
        return std::isfinite(out);
    }
    if (fn == "ellipticF" || fn == "ellipticEInc" || fn == "ellipticE") {
        const double phi = a0;
        const double m = a1;
        if (phi == 0.0) {
            out = 0.0;
            return true;
        }
        const double k = std::floor(phi / kPiDouble + 0.5);
        const double phi0 = phi - k * kPiDouble;
        const double s = std::sin(phi0);
        const double c = std::cos(phi0);
        const double s2 = s * s;
        const double c2 = c * c;
        if (1.0 - m * s2 < 0.0)
            return false;
        double baseVal = 0.0;
        if (s == 0.0) {
            baseVal = 0.0;
        } else if (fn == "ellipticF") {
            if (1.0 - m * s2 == 0.0 && c2 == 0.0)
                return false;
            double rf = 0.0;
            if (!carlsonRF(c2, 1.0 - m * s2, 1.0, rf))
                return false;
            baseVal = s * rf;
        } else {
            double rf = 0.0;
            if (!carlsonRF(c2, 1.0 - m * s2, 1.0, rf))
                return false;
            double rdTerm = 0.0;
            if (m != 0.0) {
                double rd = 0.0;
                if (!carlsonRD(c2, 1.0 - m * s2, 1.0, rd))
                    return false;
                rdTerm = (m / 3.0) * s * s2 * rd;
            }
            baseVal = s * rf - rdTerm;
        }
        if (k != 0.0) {
            double compVal = 0.0;
            const std::string compFn =
                (fn == "ellipticF") ? "ellipticK" : "ellipticE";
            if (!evalElliptic1ArgDouble(compFn, m, compVal))
                return false;
            out = 2.0 * k * compVal + baseVal;
        } else {
            out = baseVal;
        }
        return std::isfinite(out);
    }
    return false;
}

bool evalZetaDouble(double s, double &out)
{
    if (!std::isfinite(s) || s == 1.0)
        return false;
    if (s == 0.0) {
        out = -0.5;
        return true;
    }
    if (s < 0.0 && std::floor(s) == s) {
        const std::int64_t m = static_cast<std::int64_t>(-s);
        if (m % 2 == 0) {
            out = 0.0;
            return true;
        }
    }
    if (s < 0.5) {
        double zComp = 0.0;
        if (!evalZetaDouble(1.0 - s, zComp))
            return false;
        out = std::pow(2.0, s) * std::pow(kPiDouble, s - 1.0) *
              std::sin(0.5 * kPiDouble * s) * std::tgamma(1.0 - s) * zComp;
        return std::isfinite(out);
    }
    // Euler-Maclaurin summation with N = 16 and 8 Bernoulli correction terms.
    static constexpr double kB2kOverFact[8] = {
        (1.0 / 6.0) / 2.0,
        (-1.0 / 30.0) / 24.0,
        (1.0 / 42.0) / 720.0,
        (-1.0 / 30.0) / 40320.0,
        (5.0 / 66.0) / 3628800.0,
        (-691.0 / 2730.0) / 479001600.0,
        (7.0 / 6.0) / 87178291200.0,
        (-3617.0 / 510.0) / 20922789888000.0};
    constexpr int N = 16;
    double sum = 0.0;
    for (int n = 1; n < N; ++n)
        sum += std::pow(static_cast<double>(n), -s);
    const double nD = static_cast<double>(N);
    const double nPowNegS = std::pow(nD, -s);
    sum += (nD * nPowNegS) / (s - 1.0) + 0.5 * nPowNegS;

    const double invN2 = 1.0 / (nD * nD);
    double poch = s;
    double nFactor = nPowNegS / nD;
    for (int k = 1; k <= 8; ++k) {
        if (k > 1) {
            poch *= (s + static_cast<double>(2 * k - 3)) *
                    (s + static_cast<double>(2 * k - 2));
            nFactor *= invN2;
        }
        const double contrib = kB2kOverFact[k - 1] * poch * nFactor;
        sum += contrib;
        if (std::abs(contrib) <= 1e-16 * std::abs(sum))
            break;
    }
    out = sum;
    return std::isfinite(out);
}

bool evalDirichletEtaDouble(double s, double &out)
{
    if (!std::isfinite(s))
        return false;
    if (s == 1.0) {
        out = std::log(2.0);
        return true;
    }
    double z = 0.0;
    if (!evalZetaDouble(s, z))
        return false;
    out = (1.0 - std::pow(2.0, 1.0 - s)) * z;
    return std::isfinite(out);
}

bool evalPolylogDouble(double s, double z, double &out)
{
    if (!std::isfinite(s) || !std::isfinite(z) || z > 1.0)
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
        out = -std::log(1.0 - z);
        return std::isfinite(out);
    }
    if (z == 1.0) {
        if (s <= 1.0)
            return false;
        return evalZetaDouble(s, out);
    }
    if (z == -1.0) {
        double eta = 0.0;
        if (!evalDirichletEtaDouble(s, eta))
            return false;
        out = -eta;
        return std::isfinite(out);
    }
    if (s <= 0.0 && std::floor(s) == s) {
        const std::int64_t m = static_cast<std::int64_t>(-s);
        if (m == 0) {
            out = z / (1.0 - z);
            return std::isfinite(out);
        }
        if (m <= 20) {
            std::vector<double> eul(static_cast<std::size_t>(m), 0.0);
            eul[0] = 1.0;
            for (std::int64_t i = 2; i <= m; ++i) {
                for (std::int64_t k = i - 1; k >= 1; --k) {
                    eul[static_cast<std::size_t>(k)] =
                        static_cast<double>(k + 1) *
                            eul[static_cast<std::size_t>(k)] +
                        static_cast<double>(i - k) *
                            eul[static_cast<std::size_t>(k - 1)];
                }
            }
            double num = 0.0;
            for (std::int64_t k = 0; k < m; ++k) {
                num += eul[static_cast<std::size_t>(k)] *
                       std::pow(z, static_cast<double>(m - k));
            }
            out = num / std::pow(1.0 - z, static_cast<double>(m + 1));
            return std::isfinite(out);
        }
    }
    if (std::abs(z) <= 0.75) {
        double sum = 0.0;
        double zPow = z;
        for (int k = 1; k <= 160; ++k) {
            const double contrib = zPow * std::pow(static_cast<double>(k), -s);
            sum += contrib;
            if (std::abs(contrib) <= 1e-16 * std::abs(sum))
                break;
            zPow *= z;
        }
        out = sum;
        return std::isfinite(out);
    }
    if (z < 1.0 && z > -1.0) {
        double sum = 0.0;
        double zPow = z;
        for (int k = 1; k <= 800; ++k) {
            const double contrib = zPow * std::pow(static_cast<double>(k), -s);
            sum += contrib;
            if (std::abs(contrib) <= 1e-16 * std::abs(sum))
                break;
            zPow *= z;
        }
        out = sum;
        return std::isfinite(out);
    }
    return false;
}

bool evalBernoulliEuler2ArgDouble(const std::string &fn, double nVal, double x,
                                  double &out)
{
    if (!std::isfinite(nVal) || !std::isfinite(x) || std::floor(nVal) != nVal)
        return false;
    const std::int64_t n = static_cast<std::int64_t>(nVal);
    if (n < 0 || n > 40)
        return false;
    if (fn == "bernoulliB") {
        double sum = 0.0;
        double binom = 1.0;
        for (std::int64_t k = 0; k <= n; ++k) {
            if (k > 0)
                binom = (binom * static_cast<double>(n - k + 1)) /
                        static_cast<double>(k);
            Rational bk;
            if (!bernoulliExact(k, bk))
                return false;
            if (!bk.isZero()) {
                sum += binom * bk.toDouble() *
                       std::pow(x, static_cast<double>(n - k));
            }
        }
        out = sum;
        return std::isfinite(out);
    }
    if (fn == "eulerE") {
        const double xShift = x - 0.5;
        double sum = 0.0;
        double binom = 1.0;
        for (std::int64_t k = 0; k <= n; ++k) {
            if (k > 0)
                binom = (binom * static_cast<double>(n - k + 1)) /
                        static_cast<double>(k);
            Rational ek;
            if (!eulerExact(k, ek))
                return false;
            if (!ek.isZero()) {
                sum += binom * ek.toDouble() *
                       std::pow(2.0, -static_cast<double>(k)) *
                       std::pow(xShift, static_cast<double>(n - k));
            }
        }
        out = sum;
        return std::isfinite(out);
    }
    return false;
}

bool evalBetaDouble(double x, double y, double &out)
{
    if (!std::isfinite(x) || !std::isfinite(y))
        return false;
    const double xy = x + y;
    if ((x <= 0.0 && std::floor(x) == x) || (y <= 0.0 && std::floor(y) == y))
        return false;
    if (xy <= 0.0 && std::floor(xy) == xy) {
        out = 0.0;
        return true;
    }
    if (x > 0.0 && y > 0.0) {
        out = std::exp(std::lgamma(x) + std::lgamma(y) - std::lgamma(xy));
        return std::isfinite(out);
    }
    const double gx = std::tgamma(x);
    const double gy = std::tgamma(y);
    const double gxy = std::tgamma(xy);
    if (!std::isfinite(gx) || !std::isfinite(gy) || !std::isfinite(gxy) ||
        gxy == 0.0)
        return false;
    out = (gx * gy) / gxy;
    return std::isfinite(out);
}

bool evalPochhammerDouble(double a, double n, double &out)
{
    if (!std::isfinite(a) || !std::isfinite(n))
        return false;
    if (std::floor(n) == n && n >= 0.0 && n <= 60.0) {
        const int k = static_cast<int>(n);
        double prod = 1.0;
        for (int j = 0; j < k; ++j)
            prod *= (a + static_cast<double>(j));
        out = prod;
        return std::isfinite(out);
    }
    const double an = a + n;
    if ((a <= 0.0 && std::floor(a) == a) || (an <= 0.0 && std::floor(an) == an))
        return false;
    if (a > 0.0 && an > 0.0) {
        out = std::exp(std::lgamma(an) - std::lgamma(a));
        return std::isfinite(out);
    }
    out = std::tgamma(an) / std::tgamma(a);
    return std::isfinite(out);
}

bool evalIncompleteGammaDouble(const std::string &fn, double s, double x,
                               double &out)
{
    if (!std::isfinite(s) || !std::isfinite(x) || x < 0.0 || s <= 0.0)
        return false;
    if (x == 0.0) {
        out = (fn == "gammainc") ? 0.0 : std::tgamma(s);
        return std::isfinite(out);
    }
    const double gs = std::tgamma(s);
    if (!std::isfinite(gs))
        return false;
    double lower = 0.0, upper = 0.0;
    if (x < s + 1.0) {
        double sum = 1.0 / s;
        double term = sum;
        for (int k = 1; k <= 300; ++k) {
            term *= x / (s + static_cast<double>(k));
            sum += term;
            if (std::abs(term) <= 1e-16 * std::abs(sum))
                break;
        }
        lower = std::pow(x, s) * std::exp(-x) * sum;
        upper = gs - lower;
    } else {
        // Legendre continued fraction for upper incomplete gamma via Lentz's method.
        constexpr double tiny = 1e-30;
        double b = x + 1.0 - s;
        double c = 1.0 / tiny;
        double d = 1.0 / b;
        double h = d;
        for (int i = 1; i <= 300; ++i) {
            const double an = -static_cast<double>(i) * (static_cast<double>(i) - s);
            b += 2.0;
            d = an * d + b;
            if (std::abs(d) < tiny)
                d = tiny;
            c = b + an / c;
            if (std::abs(c) < tiny)
                c = tiny;
            d = 1.0 / d;
            const double del = d * c;
            h *= del;
            if (std::abs(del - 1.0) <= 1e-16)
                break;
        }
        upper = std::pow(x, s) * std::exp(-x) * h;
        lower = gs - upper;
    }
    out = (fn == "gammainc") ? lower : upper;
    return std::isfinite(out);
}

bool evalHypergeom0F1Double(double b, double z, double &out)
{
    if (!std::isfinite(b) || !std::isfinite(z))
        return false;
    if (b <= 0.0 && std::floor(b) == b)
        return false;
    double sum = 1.0, term = 1.0;
    for (int k = 1; k <= 300; ++k) {
        const double den = (b + static_cast<double>(k - 1)) * static_cast<double>(k);
        if (den == 0.0)
            return false;
        term *= z / den;
        sum += term;
        if (std::abs(term) <= 1e-16 * std::abs(sum) && k > std::abs(z))
            break;
    }
    out = sum;
    return std::isfinite(out);
}

bool evalHypergeom1F1Double(double a, double b, double z, double &out)
{
    if (!std::isfinite(a) || !std::isfinite(b) || !std::isfinite(z))
        return false;
    if (z == 0.0 || a == 0.0) {
        out = 1.0;
        return true;
    }
    const bool aNegInt = (a <= 0.0 && std::floor(a) == a);
    if (b <= 0.0 && std::floor(b) == b) {
        if (!aNegInt || b < a)
            return false;
    }
    if (!aNegInt && z < -15.0) {
        // Kummer's 1st transformation: 1F1(a, b, z) = exp(z) * 1F1(b - a, b, -z)
        double kVal = 0.0;
        if (!evalHypergeom1F1Double(b - a, b, -z, kVal))
            return false;
        out = std::exp(z) * kVal;
        return std::isfinite(out);
    }
    const int maxSteps = aNegInt ? static_cast<int>(-a) : 400;
    double sum = 1.0, term = 1.0;
    for (int k = 1; k <= maxSteps; ++k) {
        const double num = a + static_cast<double>(k - 1);
        const double den = (b + static_cast<double>(k - 1)) * static_cast<double>(k);
        if (den == 0.0)
            return false;
        term *= (num * z) / den;
        sum += term;
        if (!aNegInt && std::abs(term) <= 1e-16 * std::abs(sum) &&
            k > std::abs(z))
            break;
    }
    out = sum;
    return std::isfinite(out);
}

bool evalHypergeom2F1Double(double a, double b, double c, double z, double &out)
{
    if (!std::isfinite(a) || !std::isfinite(b) || !std::isfinite(c) ||
        !std::isfinite(z))
        return false;
    if (z == 0.0 || a == 0.0 || b == 0.0) {
        out = 1.0;
        return true;
    }
    const bool aNegInt = (a <= 0.0 && std::floor(a) == a && a >= -200.0);
    const bool bNegInt = (b <= 0.0 && std::floor(b) == b && b >= -200.0);
    const bool terminates = aNegInt || bNegInt;
    int termCount = 500;
    if (aNegInt && bNegInt)
        termCount = static_cast<int>(std::min(-a, -b));
    else if (aNegInt)
        termCount = static_cast<int>(-a);
    else if (bNegInt)
        termCount = static_cast<int>(-b);

    if (!terminates) {
        if (c <= 0.0 && std::floor(c) == c)
            return false;
        if (z > 1.0)
            return false;
        if (z == 1.0) {
            const double cab = c - a - b;
            if (cab <= 0.0)
                return false;
            out = (std::tgamma(c) * std::tgamma(cab)) /
                  (std::tgamma(c - a) * std::tgamma(c - b));
            return std::isfinite(out);
        }
        if (z < -0.5) {
            // Pfaff transformation: 2F1(a, b; c; z) = (1 - z)^(-a) * 2F1(a, c - b; c; z / (z - 1))
            const double w = z / (z - 1.0);
            double pfVal = 0.0;
            if (!evalHypergeom2F1Double(a, c - b, c, w, pfVal))
                return false;
            out = std::pow(1.0 - z, -a) * pfVal;
            return std::isfinite(out);
        }
    }

    double sum = 1.0, term = 1.0;
    for (int k = 1; k <= termCount; ++k) {
        const double num =
            (a + static_cast<double>(k - 1)) * (b + static_cast<double>(k - 1));
        const double den =
            (c + static_cast<double>(k - 1)) * static_cast<double>(k);
        if (den == 0.0)
            return false;
        term *= (num * z) / den;
        sum += term;
        if (!terminates && std::abs(term) <= 1e-16 * std::abs(sum))
            break;
    }
    out = sum;
    return std::isfinite(out);
}

bool evalDoubleRec(
    const Ctx &c, Expr e,
    const std::vector<std::pair<std::string, double>> &vals,
    std::unordered_map<std::uint32_t, double> &memo, double &out)
{
    if (e.isNull())
        return false;
    const std::uint32_t nid = c.id(e);
    const auto hit = memo.find(nid);
    if (hit != memo.end()) {
        out = hit->second;
        return true;
    }

    double res = 0.0;
    switch (c.kind(e)) {
    case NodeKind::Number:
        res = c.numberValue(e).toDouble();
        if (!std::isfinite(res))
            return false;
        break;
    case NodeKind::Symbol: {
        const std::string &name = c.symbolName(e);
        bool found = false;
        for (const auto &kv : vals) {
            if (kv.first == name) {
                res = kv.second;
                found = true;
                break;
            }
        }
        if (!found) {
            if (name == "pi" || name == "Pi") {
                res = 3.141592653589793238462643383279502884;
                found = true;
            } else if (name == "e" || name == "E") {
                res = 2.718281828459045235360287471352662498;
                found = true;
            } else if (name == "euler_gamma" || name == "EulerGamma") {
                res = kEulerGamma;
                found = true;
            }
        }
        if (!found || !std::isfinite(res))
            return false;
        break;
    }
    case NodeKind::RootOf: {
        const std::vector<Rational> &poly = c.rootOfPoly(e);
        const int idx = c.rootOfIndex(e);
        UPoly p = UPoly(poly).squarefreePart();
        p.makeMonic();
        const std::vector<RootInterval> ivs = isolateRealRoots(p);
        if (idx < 0 || idx >= static_cast<int>(ivs.size()))
            return false;
        const RootInterval iv =
            refineRoot(p, ivs[static_cast<std::size_t>(idx)],
                       Rational(std::int64_t{1}, BigInt(1) << 56));
        const Rational mid =
            (iv.lo + iv.hi) * Rational(std::int64_t{1}, BigInt(2));
        res = mid.toDouble();
        if (!std::isfinite(res))
            return false;
        break;
    }
    case NodeKind::Pow: {
        double b = 0.0;
        if (!evalDoubleRec(c, c.child(e, 0), vals, memo, b))
            return false;
        const Expr expNode = c.child(e, 1);
        if (c.kind(expNode) == NodeKind::Number) {
            const Rational &er = c.numberValue(expNode);
            std::int64_t p = 0, q = 0;
            if (er.den() == BigInt(1) && er.num().fitsInt64(p)) {
                if (b == 0.0 && p <= 0)
                    return false;
                res = std::pow(b, static_cast<double>(p));
                if (!std::isfinite(res))
                    return false;
                break;
            }
            if (er.num().fitsInt64(p) && er.den().fitsInt64(q) && q > 0) {
                if (b < 0.0) {
                    if (q % 2 == 0)
                        return false; // even root of negative is non-real
                    const double mag = std::pow(-b, er.toDouble());
                    res = (p % 2 != 0) ? -mag : mag;
                    if (!std::isfinite(res))
                        return false;
                    break;
                }
                if (b == 0.0 && p <= 0)
                    return false;
            }
        }
        double ex = 0.0;
        if (!evalDoubleRec(c, expNode, vals, memo, ex))
            return false;
        if (b < 0.0 && std::floor(ex) != ex)
            return false;
        if (b == 0.0 && ex <= 0.0)
            return false;
        res = std::pow(b, ex);
        if (!std::isfinite(res))
            return false;
        break;
    }
    case NodeKind::Func: {
        const std::string &fn = c.funcName(e);
        if (c.childCount(e) == 4 && fn == "hypergeom2F1") {
            double a0 = 0.0, a1 = 0.0, a2 = 0.0, a3 = 0.0;
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
            double a0 = 0.0, a1 = 0.0, a2 = 0.0;
            if (!evalDoubleRec(c, c.child(e, 0), vals, memo, a0) ||
                !evalDoubleRec(c, c.child(e, 1), vals, memo, a1) ||
                !evalDoubleRec(c, c.child(e, 2), vals, memo, a2) ||
                !evalHypergeom1F1Double(a0, a1, a2, res)) {
                return false;
            }
            break;
        }
        if (c.childCount(e) == 2) {
            double a0 = 0.0, a1 = 0.0;
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
                if (std::floor(a0) != a0 || std::floor(a1) != a1 ||
                    a0 < 0.0 || a0 > 50.0)
                    return false;
                const auto nInt = static_cast<std::int64_t>(a0);
                const auto kInt = static_cast<std::int64_t>(a1);
                if (kInt < 0 || kInt > nInt) {
                    res = 0.0;
                } else if (nInt == 0 && kInt == 0) {
                    res = 1.0;
                } else if (kInt == 0) {
                    res = 0.0;
                } else {
                    std::vector<BigInt> row(
                        static_cast<std::size_t>(kInt + 1), BigInt(0));
                    row[0] = BigInt(1);
                    for (std::int64_t i = 1; i <= nInt; ++i) {
                        const std::int64_t jMax = std::min(i, kInt);
                        for (std::int64_t j = jMax; j >= 1; --j) {
                            const auto ju = static_cast<std::size_t>(j);
                            if (fn == "stirlingS1") {
                                row[ju] =
                                    row[ju - 1] - BigInt(i - 1) * row[ju];
                            } else {
                                row[ju] = BigInt(j) * row[ju] + row[ju - 1];
                            }
                        }
                        row[0] = BigInt(0);
                    }
                    res = Rational(row[static_cast<std::size_t>(kInt)],
                                   BigInt(1))
                              .toDouble();
                }
            } else {
                return false;
            }
            if (!std::isfinite(res))
                return false;
            break;
        }
        double a = 0.0;
        if (!evalDoubleRec(c, c.child(e, 0), vals, memo, a))
            return false;
        if (fn == "exp") {
            res = std::exp(a);
        } else if (fn == "log") {
            if (a <= 0.0) return false;
            res = std::log(a);
        } else if (fn == "sqrt") {
            if (a < 0.0) return false;
            res = std::sqrt(a);
        } else if (fn == "abs") {
            res = std::abs(a);
        } else if (fn == "sin") {
            res = std::sin(a);
        } else if (fn == "cos") {
            res = std::cos(a);
        } else if (fn == "tan") {
            res = std::tan(a);
        } else if (fn == "cot") {
            const double t = std::tan(a);
            if (t == 0.0) return false;
            res = 1.0 / t;
        } else if (fn == "sec") {
            const double cs = std::cos(a);
            if (cs == 0.0) return false;
            res = 1.0 / cs;
        } else if (fn == "csc") {
            const double sn = std::sin(a);
            if (sn == 0.0) return false;
            res = 1.0 / sn;
        } else if (fn == "asin") {
            if (a < -1.0 || a > 1.0) return false;
            res = std::asin(a);
        } else if (fn == "acos") {
            if (a < -1.0 || a > 1.0) return false;
            res = std::acos(a);
        } else if (fn == "atan") {
            res = std::atan(a);
        } else if (fn == "acot") {
            res = (a >= 0.0) ? std::atan(1.0 / a)
                             : (3.141592653589793238462643383279502884 +
                                std::atan(1.0 / a));
        } else if (fn == "asec") {
            if (a > -1.0 && a < 1.0) return false;
            res = std::acos(1.0 / a);
        } else if (fn == "acsc") {
            if (a > -1.0 && a < 1.0) return false;
            res = std::asin(1.0 / a);
        } else if (fn == "sinh") {
            res = std::sinh(a);
        } else if (fn == "cosh") {
            res = std::cosh(a);
        } else if (fn == "tanh") {
            res = std::tanh(a);
        } else if (fn == "coth") {
            const double th = std::tanh(a);
            if (th == 0.0) return false;
            res = 1.0 / th;
        } else if (fn == "sech") {
            res = 1.0 / std::cosh(a);
        } else if (fn == "csch") {
            const double sh = std::sinh(a);
            if (sh == 0.0) return false;
            res = 1.0 / sh;
        } else if (fn == "asinh") {
            res = std::asinh(a);
        } else if (fn == "acosh") {
            if (a < 1.0) return false;
            res = std::acosh(a);
        } else if (fn == "atanh") {
            if (a <= -1.0 || a >= 1.0) return false;
            res = std::atanh(a);
        } else if (fn == "acoth") {
            if (a >= -1.0 && a <= 1.0) return false;
            res = std::atanh(1.0 / a);
        } else if (fn == "asech") {
            if (a <= 0.0 || a > 1.0) return false;
            res = std::acosh(1.0 / a);
        } else if (fn == "acsch") {
            if (a == 0.0) return false;
            res = std::asinh(1.0 / a);
        } else if (fn == "erf") {
            res = std::erf(a);
        } else if (fn == "erfc") {
            res = std::erfc(a);
        } else if (fn == "erfi") {
            res = evalErfiDouble(a);
        } else if (fn == "Ei") {
            if (!evalEiDouble(a, res)) return false;
        } else if (fn == "li") {
            if (a == 0.0) {
                res = 0.0;
            } else {
                if (a < 0.0 || a == 1.0) return false;
                if (!evalEiDouble(std::log(a), res)) return false;
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
            if (a <= 0.0 && std::floor(a) == a) return false;
            res = std::tgamma(a);
        } else if (fn == "factorial") {
            if (a < 0.0 && std::floor(a) == a) return false;
            res = std::tgamma(a + 1.0);
        } else if (fn == "lgamma" || fn == "loggamma") {
            if (a <= 0.0) return false;
            res = std::lgamma(a);
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
            if (std::floor(a) != a) return false;
            Rational rVal;
            const std::int64_t nInt = static_cast<std::int64_t>(a);
            if (!(fn == "bernoulliB" ? bernoulliExact(nInt, rVal)
                                     : eulerExact(nInt, rVal)))
                return false;
            res = rVal.toDouble();
        } else {
            return false;
        }
        if (!std::isfinite(res))
            return false;
        break;
    }
    case NodeKind::Add:
    case NodeKind::Mul: {
        const bool isAdd = (c.kind(e) == NodeKind::Add);
        res = isAdd ? 0.0 : 1.0;
        for (std::size_t i = 0; i < c.childCount(e); ++i) {
            double t = 0.0;
            if (!evalDoubleRec(c, c.child(e, i), vals, memo, t))
                return false;
            res = isAdd ? (res + t) : (res * t);
            if (!std::isfinite(res))
                return false;
        }
        break;
    }
    }

    memo.emplace(nid, res);
    out = res;
    return true;
}

} // namespace

bool Ctx::evalDouble(
    Expr e, const std::vector<std::pair<std::string, double>> &vals,
    double &out) const
{
    std::unordered_map<std::uint32_t, double> memo;
    return evalDoubleRec(*this, e, vals, memo, out);
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
    case NodeKind::Func: {
        std::vector<Expr> args;
        args.reserve(childCount(e));
        for (std::size_t i = 0; i < childCount(e); ++i)
            args.push_back(expand(child(e, i)));
        const std::string &fn = funcName(e);
        if (args.size() == 2 && kind(args[0]) == NodeKind::Number) {
            const Rational &rn = numberValue(args[0]);
            std::int64_t n = 0;
            if (rn.den() == BigInt(1) && rn.num().fitsInt64(n)) {
                const Expr xArg = args[1];
                if (fn == "legendreP") {
                    if (n < 0) n = -n - 1;
                    if (n >= 0 && n <= 64) {
                        if (n == 0) return one();
                        if (n == 1) return xArg;
                        Expr pPrev = one(), pCur = xArg;
                        for (std::int64_t k = 1; k < n; ++k) {
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
                        for (std::int64_t k = 1; k < n; ++k) {
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
                        for (std::int64_t k = 1; k < n; ++k) {
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
                        for (std::int64_t k = 1; k < n; ++k) {
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
                        for (std::int64_t k = 1; k < n; ++k) {
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
                    std::vector<Expr> terms;
                    BigInt binom(1);
                    for (std::int64_t k = 0; k <= n; ++k) {
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
                    std::vector<Expr> terms;
                    BigInt binom(1);
                    for (std::int64_t k = 0; k <= n; ++k) {
                        if (k > 0)
                            binom = (binom * BigInt(n - k + 1)) / BigInt(k);
                        Rational ek;
                        if (eulerExact(k, ek) && !ek.isZero()) {
                            const BigInt twoPow = BigInt::powUInt(
                                BigInt(2), static_cast<std::size_t>(k));
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
                    for (std::int64_t k = 2; k <= n - 1; ++k)
                        nFact = nFact * BigInt(k);
                    std::vector<Expr> sumTerms;
                    BigInt kFact(1);
                    for (std::int64_t k = 0; k < n; ++k) {
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
            std::int64_t kCount = 0;
            if (numberValue(args[1]).num().fitsInt64(kCount) &&
                std::abs(kCount) <= 20) {
                if (kCount == 0)
                    return one();
                if (kCount > 0) {
                    std::vector<Expr> factors;
                    factors.reserve(static_cast<std::size_t>(kCount));
                    for (std::int64_t j = 0; j < kCount; ++j)
                        factors.push_back(add({args[0], number(j)}));
                    return expand(mul(factors));
                }
                std::vector<Expr> denFactors;
                bool okDen = true;
                for (std::int64_t j = 1; j <= -kCount; ++j) {
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
            for (int side = 0; side < 2; ++side) {
                const Expr nSide = args[static_cast<std::size_t>(side)];
                const Expr xSide = args[static_cast<std::size_t>(1 - side)];
                if (kind(nSide) == NodeKind::Number &&
                    numberValue(nSide).den() == BigInt(1)) {
                    std::int64_t nInt = 0;
                    if (numberValue(nSide).num().fitsInt64(nInt) &&
                        nInt >= 1 && nInt <= 20) {
                        BigInt fact(1);
                        std::vector<Expr> denFactors;
                        bool okDen = true;
                        for (std::int64_t k = 0; k < nInt; ++k) {
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
            std::int64_t ma = 0;
            if (numberValue(args[0]).num().fitsInt64(ma) && -ma <= 12) {
                const std::int64_t mTerm = -ma;
                std::vector<Expr> terms{one()};
                Expr numPoch = one();
                Expr denPoch = one();
                BigInt fact(1);
                bool okDen = true;
                for (std::int64_t k = 1; k <= mTerm; ++k) {
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
            std::int64_t mTerm = -1;
            for (std::size_t idx = 0; idx < 2; ++idx) {
                if (kind(args[idx]) == NodeKind::Number &&
                    numberValue(args[idx]).den() == BigInt(1) &&
                    numberValue(args[idx]).signum() <= 0) {
                    std::int64_t mv = 0;
                    if (numberValue(args[idx]).num().fitsInt64(mv) &&
                        -mv <= 12 && (mTerm < 0 || -mv < mTerm)) {
                        mTerm = -mv;
                    }
                }
            }
            if (mTerm >= 0) {
                std::vector<Expr> terms{one()};
                Expr aPoch = one(), bPoch = one(), cPoch = one();
                BigInt fact(1);
                bool okDen = true;
                for (std::int64_t k = 1; k <= mTerm; ++k) {
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
            for (const Expr &t : terms) {
                for (const Expr &f : factors) {
                    const Expr prod = mul({t, f});
                    bool hasAddFactor = (kind(prod) == NodeKind::Add);
                    if (kind(prod) == NodeKind::Mul) {
                        for (std::size_t j = 0; j < childCount(prod); ++j) {
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
            for (const Expr &t : terms) {
                for (const Expr &f : factors) {
                    const Expr prod = mul({t, f});
                    bool hasAddFactor = (kind(prod) == NodeKind::Add);
                    if (kind(prod) == NodeKind::Mul) {
                        for (std::size_t j = 0; j < childCount(prod); ++j) {
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
    case NodeKind::Func: {
        std::vector<Expr> kids;
        kids.reserve(childCount(e));
        for (std::size_t i = 0; i < childCount(e); ++i)
            kids.push_back(subs(child(e, i), from, to));
        return func(funcName(e), kids);
    }
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

std::size_t Ctx::leafCount(Expr e) const
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
        std::size_t total = 1;
        for (std::size_t i = 0; i < childCount(e); ++i)
            total += leafCount(child(e, i));
        return total;
    }
    }
    return 1;
}

namespace {

bool isElementaryFuncName(const std::string &name)
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

std::size_t Ctx::exprCost(Expr e) const
{
    if (e.isNull())
        return 0;
    std::unordered_map<std::uint32_t, bool> visited;
    std::size_t total = 0;

    struct Frame
    {
        Expr expr;
        bool insideLog;
    };
    std::vector<Frame> stack{Frame{e, false}};
    while (!stack.empty()) {
        const Frame cur = stack.back();
        stack.pop_back();
        if (cur.expr.isNull())
            continue;
        const std::uint32_t nid = id(cur.expr);
        auto it = visited.find(nid);
        if (it != visited.end()) {
            // If an `abs` node was previously visited outside `log` (cost 3)
            // and is now also reached directly inside `log` (cost 5), upgrade
            // its weight by +2 once.
            if (cur.insideLog && !it->second &&
                kind(cur.expr) == NodeKind::Func &&
                funcName(cur.expr) == "abs") {
                it->second = true;
                total += 2;
            }
            continue;
        }
        const NodeKind k = kind(cur.expr);
        bool markedInsideLog = false;
        if (k == NodeKind::Func) {
            const std::string &fn = funcName(cur.expr);
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
        visited.emplace(nid, markedInsideLog);
        const bool nextInsideLog =
            (k == NodeKind::Func && funcName(cur.expr) == "log");
        for (std::size_t i = 0; i < childCount(cur.expr); ++i)
            stack.push_back(Frame{child(cur.expr, i), nextInsideLog});
    }
    return total;
}

void Ctx::assume(const std::string &name, AssumeDomain dom)
{
    if (dom == AssumeDomain::Any)
        assumptions_.erase(name);
    else
        assumptions_[name] = dom;
}

void Ctx::assume(Expr sym, AssumeDomain dom)
{
    assert(!sym.isNull() && kind(sym) == NodeKind::Symbol);
    if (!sym.isNull() && kind(sym) == NodeKind::Symbol)
        assume(symbolName(sym), dom);
}

AssumeDomain Ctx::assumption(const std::string &name) const
{
    auto it = assumptions_.find(name);
    return it != assumptions_.end() ? it->second : AssumeDomain::Any;
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
        const std::string &nm = symbolName(e);
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
        const std::string &fn = funcName(e);
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
        int sign = 1;
        for (std::size_t i = 0; i < childCount(e); ++i) {
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
        for (std::size_t i = 0; i < childCount(e); ++i) {
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
        const std::string &fn = funcName(e);
        const Expr u = child(e, 0);
        if (fn == "sinh" || fn == "tanh" || fn == "asinh" || fn == "atan" ||
            fn == "erf" || fn == "erfi" || fn == "Si" || fn == "FresnelS" ||
            fn == "FresnelC")
            return isAssumedNegative(u);
        return false;
    }
    case NodeKind::Mul: {
        int sign = 1;
        for (std::size_t i = 0; i < childCount(e); ++i) {
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
        for (std::size_t i = 0; i < childCount(e); ++i) {
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
        const std::string &fn = funcName(e);
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
        int negCount = 0;
        for (std::size_t i = 0; i < childCount(e); ++i) {
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
        for (std::size_t i = 0; i < childCount(e); ++i)
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
        const std::string &nm = symbolName(e);
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
        const std::string &fn = funcName(e);
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
        for (std::size_t i = 0; i < childCount(e); ++i)
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
        for (std::size_t i = 0; i < childCount(e); ++i)
            if (!isAssumedInteger(child(e, i)))
                return false;
        return true;
    }
    }
    return false;
}

} // namespace numkit::cas
