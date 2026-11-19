// poly/groebner.hpp — multivariate Groebner bases (Buchberger's algorithm) over Q[x_1, ..., x_k].
#pragma once

#include <keel/array.h>
#include <keel/core.h>
#include <keel/string.h>
#include <numkit/cas/core/budget.hpp>
#include <numkit/cas/core/expr.hpp>

namespace numkit::cas {

enum class MonomialOrder
{
    Lex,     // lexicographic order: vars[0] > vars[1] > ... > vars[k-1]
    GrevLex, // graded reverse lexicographic order
};

struct GroebnerResult
{
    enum class Status
    {
        Unevaluated,
        ProvedSymbolic,
    };

    Status status = Status::Unevaluated;
    keel::Array<Expr> basis; // unique reduced monic Groebner basis
    keel::String reason;

    GroebnerResult() noexcept = default;
    GroebnerResult(const GroebnerResult &o)
        : status(o.status), basis(o.basis.clone()), reason(o.reason.clone())
    {
    }
    GroebnerResult &operator=(const GroebnerResult &o)
    {
        if (this != &o) {
            status = o.status;
            basis = o.basis.clone();
            reason = o.reason.clone();
        }
        return *this;
    }
    GroebnerResult(GroebnerResult &&) noexcept = default;
    GroebnerResult &operator=(GroebnerResult &&) noexcept = default;

    bool proved() const { return status == Status::ProvedSymbolic; }
};

// Compute the unique reduced monic Groebner basis of the polynomial ideal
// <polys> in Q[vars[0], ..., vars[k-1]] under `order`, certified by
// verifying that every S-polynomial S(g_i, g_j) and every input generator
// f_m reduces to 0 modulo `basis`.
GroebnerResult groebnerBasis(Ctx &c, keel::ArrayRef<Expr> polys,
                             keel::ArrayRef<Expr> vars,
                             MonomialOrder order = MonomialOrder::Lex,
                             Budget *budget = nullptr);

// Reduce a multivariate polynomial `f` in Q[vars] modulo a polynomial list `G`
// (such as a Groebner basis) under `order`, returning the normal form remainder.
// Returns a null Expr if `f` or any element of `G` is not a polynomial in Q[vars].
Expr polyReduceMulti(Ctx &c, Expr f, keel::ArrayRef<Expr> G,
                     keel::ArrayRef<Expr> vars,
                     MonomialOrder order = MonomialOrder::Lex,
                     Budget *budget = nullptr);

// Exact multivariate polynomial division `f / g` in Q[x_1, ..., x_k].
// If `vars` is empty, all symbol variables appearing in `f` and `g` are collected
// automatically in canonical order. Returns `q` when `f == g * q` holds exactly,
// or a null Expr if `g` does not divide `f`.
Expr divExactMulti(Ctx &c, Expr f, Expr g, keel::ArrayRef<Expr> vars = {},
                   Budget *budget = nullptr);

// Compute the canonical monic greatest common divisor gcd(f, g) in Q[x_1, ..., x_k].
// If `vars` is empty, all symbol variables appearing in `f` and `g` are collected
// automatically in canonical order.
// Certified by verifying exact polynomial divisibility `f = d * q_f` and `g = d * q_g`.
Expr gcdMulti(Ctx &c, Expr f, Expr g, keel::ArrayRef<Expr> vars = {},
              Budget *budget = nullptr);

struct FactorMultiItem
{
    Expr factor;          // monic irreducible polynomial factor in Q[x_1, ..., x_k]
    int multiplicity = 1; // positive integer multiplicity
};

struct FactorMultiResult
{
    enum class Status
    {
        Unevaluated,
        ProvedSymbolic,
    };

    Status status = Status::Unevaluated;
    Rational content{keel::i64{1}};    // rational leading/content scalar
    keel::Array<FactorMultiItem> factors; // monic irreducible factors with multiplicities
    Expr expr;                            // reconstructed factored Expr
    keel::String reason;

    FactorMultiResult() noexcept = default;
    FactorMultiResult(const FactorMultiResult &o)
        : status(o.status), content(o.content), factors(o.factors.clone()), expr(o.expr), reason(o.reason.clone())
    {
    }
    FactorMultiResult &operator=(const FactorMultiResult &o)
    {
        if (this != &o) {
            status = o.status;
            content = o.content;
            factors = o.factors.clone();
            expr = o.expr;
            reason = o.reason.clone();
        }
        return *this;
    }
    FactorMultiResult(FactorMultiResult &&) noexcept = default;
    FactorMultiResult &operator=(FactorMultiResult &&) noexcept = default;

    bool proved() const { return status == Status::ProvedSymbolic; }
};

// Factor a multivariate polynomial `f` in Q[x_1, ..., x_k] into its rational
// scalar content and monic irreducible polynomial factors with multiplicities:
//   f = content * prod_i factors[i].factor ^ factors[i].multiplicity.
// If `vars` is empty, all symbol variables appearing in `f` are collected
// automatically in canonical order.
// Certified by verifying `expand(expr - f) == 0`.
FactorMultiResult factorMulti(Ctx &c, Expr f,
                              keel::ArrayRef<Expr> vars = {},
                              Budget *budget = nullptr);

} // namespace numkit::cas
