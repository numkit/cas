// poly/groebner.hpp — multivariate Groebner bases (Buchberger's algorithm) over Q[x_1, ..., x_k].
#pragma once

#include <numkit/cas/core/budget.hpp>
#include <numkit/cas/core/expr.hpp>

#include <string>
#include <vector>

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
    std::vector<Expr> basis; // unique reduced monic Groebner basis
    std::string reason;

    bool proved() const { return status == Status::ProvedSymbolic; }
};

// Compute the unique reduced monic Groebner basis of the polynomial ideal
// <polys> in Q[vars[0], ..., vars[k-1]] under `order`, certified by
// verifying that every S-polynomial S(g_i, g_j) and every input generator
// f_m reduces to 0 modulo `basis`.
GroebnerResult groebnerBasis(Ctx &c, const std::vector<Expr> &polys,
                             const std::vector<Expr> &vars,
                             MonomialOrder order = MonomialOrder::Lex,
                             Budget *budget = nullptr);

// Reduce a multivariate polynomial `f` in Q[vars] modulo a polynomial list `G`
// (such as a Groebner basis) under `order`, returning the normal form remainder.
// Returns a null Expr if `f` or any element of `G` is not a polynomial in Q[vars].
Expr polyReduceMulti(Ctx &c, Expr f, const std::vector<Expr> &G,
                     const std::vector<Expr> &vars,
                     MonomialOrder order = MonomialOrder::Lex,
                     Budget *budget = nullptr);

} // namespace numkit::cas
