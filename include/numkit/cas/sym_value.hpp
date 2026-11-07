// include/numkit/cas/sym_value.hpp — Value bridge and BuiltinClass for numkit::cas.
#pragma once

#include <numkit/cas/core/expr.hpp>
#include <numkit/cas/linalg/symmatrix.hpp>
#include <numkit/value/object.hpp>
#include <numkit/value/span.hpp>
#include <numkit/value/value.hpp>

#include <cstddef>
#include <memory>
#include <memory_resource>
#include <string>
#include <utility>
#include <vector>

namespace numkit::cas {

struct SymPayload : public numkit::NativePayload
{
    std::shared_ptr<Ctx> ctx;
    Expr expr;

    SymPayload() = default;
    SymPayload(std::shared_ptr<Ctx> c, Expr e)
        : ctx(std::move(c)), expr(e)
    {
    }

    std::shared_ptr<numkit::NativePayload> clone() const override;
    double asDouble() const override;
    std::shared_ptr<numkit::NativePayload> fromScalarDouble(double v) const override;
};

// Shared symbolic context for the current session.
std::shared_ptr<Ctx> defaultCtx();

// Conversion helpers between numkit::Value and numkit::cas::Expr / SymMatrix.
bool isSymValue(const numkit::Value &v) noexcept;
Expr toSymExpr(const numkit::Value &v, Ctx &c, const char *fnName = "sym");
SymMatrix toSymMatrix(const numkit::Value &v, Ctx &c, const char *fnName = "sym");
std::vector<Expr> toSymVector(const numkit::Value &v, Ctx &c, const char *fnName = "sym");

numkit::Value fromSymExpr(const std::shared_ptr<Ctx> &c, Expr e,
                          std::pmr::memory_resource *mr = nullptr);
numkit::Value fromSymMatrix(const std::shared_ptr<Ctx> &c, const SymMatrix &M,
                            std::pmr::memory_resource *mr = nullptr);
numkit::Value fromSymVector(const std::shared_ptr<Ctx> &c, const std::vector<Expr> &vec,
                            bool column = true,
                            std::pmr::memory_resource *mr = nullptr);

// Construct the BuiltinClass definition for "sym".
numkit::BuiltinClass makeSymBuiltinClass();

// Value-level compute entry points (each begins with <fn>_argcheck).
numkit::Value symCreate(numkit::Span<const numkit::Value> args,
                        std::pmr::memory_resource *mr = nullptr);
void symsCommand(numkit::Span<const numkit::Value> args,
                 std::vector<std::pair<std::string, numkit::Value>> &bindingsOut,
                 std::pmr::memory_resource *mr = nullptr);
numkit::Value symAssume(const numkit::Value &symVal, const std::string &domainStr,
                        std::pmr::memory_resource *mr = nullptr);
numkit::Value symAssumptions(const numkit::Value &symVal,
                             std::pmr::memory_resource *mr = nullptr);
numkit::Value symDouble(const numkit::Value &v,
                        std::pmr::memory_resource *mr = nullptr);
numkit::Value symVpa(numkit::Span<const numkit::Value> args,
                     std::pmr::memory_resource *mr = nullptr);
numkit::Value symChar(const numkit::Value &v,
                      std::pmr::memory_resource *mr = nullptr);
numkit::Value symLatex(const numkit::Value &v,
                       std::pmr::memory_resource *mr = nullptr);
numkit::Value symCCode(const numkit::Value &v,
                       std::pmr::memory_resource *mr = nullptr);
numkit::Value symSimplify(const numkit::Value &v,
                          std::pmr::memory_resource *mr = nullptr);
numkit::Value symExpand(const numkit::Value &v,
                        std::pmr::memory_resource *mr = nullptr);
void symFactor(numkit::Span<const numkit::Value> args, std::size_t nargout,
               numkit::Span<numkit::Value> outs,
               std::pmr::memory_resource *mr = nullptr);
numkit::Value symCollect(numkit::Span<const numkit::Value> args,
                         std::pmr::memory_resource *mr = nullptr);
void symCoeffs(numkit::Span<const numkit::Value> args, std::size_t nargout,
               numkit::Span<numkit::Value> outs,
               std::pmr::memory_resource *mr = nullptr);
void symNumden(const numkit::Value &v, std::size_t nargout,
               numkit::Span<numkit::Value> outs,
               std::pmr::memory_resource *mr = nullptr);
numkit::Value symPartfrac(numkit::Span<const numkit::Value> args,
                          std::pmr::memory_resource *mr = nullptr);
numkit::Value symSubs(numkit::Span<const numkit::Value> args,
                      std::pmr::memory_resource *mr = nullptr);
numkit::Value symSymvar(numkit::Span<const numkit::Value> args,
                        std::pmr::memory_resource *mr = nullptr);
numkit::Value symPoly2sym(numkit::Span<const numkit::Value> args,
                          std::pmr::memory_resource *mr = nullptr);
numkit::Value symSym2poly(numkit::Span<const numkit::Value> args,
                          std::pmr::memory_resource *mr = nullptr);
numkit::Value symDiff(numkit::Span<const numkit::Value> args,
                      std::pmr::memory_resource *mr = nullptr);
numkit::Value symInt(numkit::Span<const numkit::Value> args,
                     std::pmr::memory_resource *mr = nullptr);
numkit::Value symLimit(numkit::Span<const numkit::Value> args,
                       std::pmr::memory_resource *mr = nullptr);
numkit::Value symTaylor(numkit::Span<const numkit::Value> args,
                        std::pmr::memory_resource *mr = nullptr);
numkit::Value symLaurent(numkit::Span<const numkit::Value> args,
                         std::pmr::memory_resource *mr = nullptr);
numkit::Value symMtaylor(numkit::Span<const numkit::Value> args,
                         std::pmr::memory_resource *mr = nullptr);
void symPade(numkit::Span<const numkit::Value> args, std::size_t nargout,
             numkit::Span<numkit::Value> outs,
             std::pmr::memory_resource *mr = nullptr);
numkit::Value symResidue(numkit::Span<const numkit::Value> args,
                         std::pmr::memory_resource *mr = nullptr);
numkit::Value symSymsum(numkit::Span<const numkit::Value> args,
                        std::pmr::memory_resource *mr = nullptr);
numkit::Value symFiniteDiff(numkit::Span<const numkit::Value> args,
                            std::pmr::memory_resource *mr = nullptr);
numkit::Value symEulerMaclaurin(numkit::Span<const numkit::Value> args,
                                std::pmr::memory_resource *mr = nullptr);
void symSolve(numkit::Span<const numkit::Value> args, std::size_t nargout,
              numkit::Span<numkit::Value> outs,
              std::pmr::memory_resource *mr = nullptr);
numkit::Value symGroebner(numkit::Span<const numkit::Value> args,
                          std::pmr::memory_resource *mr = nullptr);
numkit::Value symPolyReduce(numkit::Span<const numkit::Value> args,
                            std::pmr::memory_resource *mr = nullptr);
numkit::Value symDsolve(numkit::Span<const numkit::Value> args,
                        std::pmr::memory_resource *mr = nullptr);
numkit::Value symPdsolve(numkit::Span<const numkit::Value> args,
                         std::pmr::memory_resource *mr = nullptr);
numkit::Value symLaplace(numkit::Span<const numkit::Value> args,
                         std::pmr::memory_resource *mr = nullptr);
numkit::Value symIlaplace(numkit::Span<const numkit::Value> args,
                          std::pmr::memory_resource *mr = nullptr);
numkit::Value symFourier(numkit::Span<const numkit::Value> args,
                         std::pmr::memory_resource *mr = nullptr);
numkit::Value symIfourier(numkit::Span<const numkit::Value> args,
                          std::pmr::memory_resource *mr = nullptr);
numkit::Value symZtrans(numkit::Span<const numkit::Value> args,
                        std::pmr::memory_resource *mr = nullptr);
numkit::Value symIztrans(numkit::Span<const numkit::Value> args,
                         std::pmr::memory_resource *mr = nullptr);
numkit::Value symRsolve(numkit::Span<const numkit::Value> args,
                        std::pmr::memory_resource *mr = nullptr);
numkit::Value symDet(const numkit::Value &A,
                     std::pmr::memory_resource *mr = nullptr);
numkit::Value symInv(const numkit::Value &A,
                     std::pmr::memory_resource *mr = nullptr);
numkit::Value symTrace(const numkit::Value &A,
                       std::pmr::memory_resource *mr = nullptr);
numkit::Value symAdjugate(const numkit::Value &A,
                          std::pmr::memory_resource *mr = nullptr);
numkit::Value symCharpoly(numkit::Span<const numkit::Value> args,
                          std::pmr::memory_resource *mr = nullptr);
numkit::Value symRank(const numkit::Value &A,
                      std::pmr::memory_resource *mr = nullptr);
void symRref(const numkit::Value &A, std::size_t nargout,
             numkit::Span<numkit::Value> outs,
             std::pmr::memory_resource *mr = nullptr);
numkit::Value symNull(const numkit::Value &A,
                      std::pmr::memory_resource *mr = nullptr);
numkit::Value symLinsolve(const numkit::Value &A, const numkit::Value &B,
                          std::pmr::memory_resource *mr = nullptr);
void symLu(const numkit::Value &A, std::size_t nargout,
           numkit::Span<numkit::Value> outs,
           std::pmr::memory_resource *mr = nullptr);
void symQr(const numkit::Value &A, std::size_t nargout,
           numkit::Span<numkit::Value> outs,
           std::pmr::memory_resource *mr = nullptr);
void symEig(const numkit::Value &A, std::size_t nargout,
            numkit::Span<numkit::Value> outs,
            std::pmr::memory_resource *mr = nullptr);
void symJordan(const numkit::Value &A, std::size_t nargout,
               numkit::Span<numkit::Value> outs,
               std::pmr::memory_resource *mr = nullptr);
numkit::Value symExpm(numkit::Span<const numkit::Value> args,
                      std::pmr::memory_resource *mr = nullptr);
numkit::Value symJacobian(numkit::Span<const numkit::Value> args,
                          std::pmr::memory_resource *mr = nullptr);
numkit::Value symGradient(numkit::Span<const numkit::Value> args,
                          std::pmr::memory_resource *mr = nullptr);
numkit::Value symHessian(numkit::Span<const numkit::Value> args,
                         std::pmr::memory_resource *mr = nullptr);
numkit::Value symDivergence(const numkit::Value &F, const numkit::Value &vars,
                            std::pmr::memory_resource *mr = nullptr);
numkit::Value symCurl(const numkit::Value &F, const numkit::Value &vars,
                      std::pmr::memory_resource *mr = nullptr);
numkit::Value symLaplacian(numkit::Span<const numkit::Value> args,
                           std::pmr::memory_resource *mr = nullptr);
numkit::Value symWronskian(numkit::Span<const numkit::Value> args,
                           std::pmr::memory_resource *mr = nullptr);
numkit::Value symPotential(const numkit::Value &F, const numkit::Value &vars,
                           std::pmr::memory_resource *mr = nullptr);
numkit::Value symEulerLagrange(numkit::Span<const numkit::Value> args,
                               std::pmr::memory_resource *mr = nullptr);
numkit::Value symHamiltonian(numkit::Span<const numkit::Value> args,
                             std::pmr::memory_resource *mr = nullptr);
numkit::Value symLegendreTransform(numkit::Span<const numkit::Value> args,
                                   std::pmr::memory_resource *mr = nullptr);
numkit::Value symPoissonBracket(numkit::Span<const numkit::Value> args,
                                std::pmr::memory_resource *mr = nullptr);
numkit::Value symLagrangeExtrema(numkit::Span<const numkit::Value> args,
                                 std::pmr::memory_resource *mr = nullptr);
numkit::Value symFrenetSerret(numkit::Span<const numkit::Value> args,
                              std::pmr::memory_resource *mr = nullptr);
numkit::Value symSurfaceCurvature(numkit::Span<const numkit::Value> args,
                                  std::pmr::memory_resource *mr = nullptr);
numkit::Value symChristoffel(const numkit::Value &metric, const numkit::Value &coords,
                             std::pmr::memory_resource *mr = nullptr);
numkit::Value symRiemann(const numkit::Value &metric, const numkit::Value &coords,
                         std::pmr::memory_resource *mr = nullptr);
numkit::Value symRicci(const numkit::Value &metric, const numkit::Value &coords,
                       std::pmr::memory_resource *mr = nullptr);
numkit::Value symScalarCurvature(const numkit::Value &metric, const numkit::Value &coords,
                                 std::pmr::memory_resource *mr = nullptr);
numkit::Value symGeodesic(numkit::Span<const numkit::Value> args,
                          std::pmr::memory_resource *mr = nullptr);
numkit::Value symLineIntegral(numkit::Span<const numkit::Value> args,
                              std::pmr::memory_resource *mr = nullptr);
numkit::Value symSurfaceIntegral(numkit::Span<const numkit::Value> args,
                                 std::pmr::memory_resource *mr = nullptr);
numkit::Value symElemFunc1(const std::string &fnName, const numkit::Value &v,
                           std::pmr::memory_resource *mr = nullptr);
numkit::Value symElemFunc2(const std::string &fnName, const numkit::Value &a,
                           const numkit::Value &b,
                           std::pmr::memory_resource *mr = nullptr);

} // namespace numkit::cas
