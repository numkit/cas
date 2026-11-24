// include/numkit/cas/sym_value.hpp — Value bridge and BuiltinClass for numkit::cas.
#pragma once

#include <keel/array.h>
#include <keel/core.h>
#include <keel/memory.h>
#include <keel/ref.h>
#include <keel/smart_ptr.h>
#include <keel/string.h>
#include <keel/cas/core/expr.hpp>
#include <keel/cas/linalg/symmatrix.hpp>
#include <numkit/value/object.hpp>
#include <numkit/value/value.hpp>


namespace numkit::cas {

using keel::cas::Ctx;
using keel::cas::Expr;
using keel::cas::SymMatrix;

struct SymPayload : public numkit::NativePayload
{
    keel::Arc<Ctx> ctx;
    Expr expr;
    keel::Array<Expr> funParams;

    SymPayload() = default;
    SymPayload(keel::Arc<Ctx> c, Expr e)
        : ctx(keel::move(c)), expr(e)
    {
    }
    SymPayload(keel::Arc<Ctx> c, Expr e, keel::Array<Expr> params)
        : ctx(keel::move(c)), expr(e), funParams(keel::move(params))
    {
    }

    keel::Arc<numkit::NativePayload> clone(keel::Allocator *alloc = nullptr) const override;
    keel::f64 asDouble() const override;
    keel::Arc<numkit::NativePayload> fromScalarDouble(keel::f64 v,
                                                      keel::Allocator *alloc = nullptr) const override;
};

// Shared symbolic context for the current session.
keel::Arc<Ctx> defaultCtx();

// Conversion helpers between numkit::Value and numkit::cas::Expr / SymMatrix.
bool isSymValue(const numkit::Value &v) noexcept;
bool isSymfunValue(const numkit::Value &v) noexcept;
Expr toSymExpr(const numkit::Value &v, Ctx &c, const char *fnName = "sym");
SymMatrix toSymMatrix(const numkit::Value &v, Ctx &c, const char *fnName = "sym");
keel::Array<Expr> toSymVector(const numkit::Value &v, Ctx &c, const char *fnName = "sym");

numkit::Value fromSymExpr(const keel::Arc<Ctx> &c, Expr e,
                          keel::Allocator *mr = nullptr);
numkit::Value fromSymfunExpr(const keel::Arc<Ctx> &c, Expr e,
                             keel::ArrayRef<Expr> params,
                             keel::Allocator *mr = nullptr);
numkit::Value fromSymMatrix(const keel::Arc<Ctx> &c, const SymMatrix &M,
                            keel::Allocator *mr = nullptr);
numkit::Value fromSymVector(const keel::Arc<Ctx> &c, keel::ArrayRef<Expr> vec,
                            bool column = true,
                            keel::Allocator *mr = nullptr);

// Construct the BuiltinClass definitions for "sym" and "symfun".
numkit::BuiltinClass makeSymBuiltinClass();
numkit::BuiltinClass makeSymfunBuiltinClass();

// Value-level compute entry points (each begins with <fn>_argcheck).
numkit::Value symCreate(keel::ArrayRef<numkit::Value> args,
                        keel::Allocator *mr = nullptr);
numkit::Value symfunCreate(keel::ArrayRef<numkit::Value> args,
                           keel::Allocator *mr = nullptr);
numkit::Value symFormula(const numkit::Value &v,
                         keel::Allocator *mr = nullptr);
numkit::Value symArgnames(const numkit::Value &v,
                          keel::Allocator *mr = nullptr);
numkit::Value symLhs(const numkit::Value &v,
                     keel::Allocator *mr = nullptr);
numkit::Value symRhs(const numkit::Value &v,
                     keel::Allocator *mr = nullptr);
numkit::Value symIsAlways(const numkit::Value &v,
                          keel::Allocator *mr = nullptr);
keel::String symMatlabFunctionSource(keel::ArrayRef<numkit::Value> args,
                                     keel::Allocator *mr = nullptr);
void symsCommand(keel::ArrayRef<numkit::Value> args,
                 keel::Array<keel::Pair<keel::String, numkit::Value>> &bindingsOut,
                 keel::Allocator *mr = nullptr);
numkit::Value symAssume(const numkit::Value &symVal, keel::StringRef domainStr,
                        keel::Allocator *mr = nullptr);
numkit::Value symAssumeCond(const numkit::Value &condVal,
                            keel::Allocator *mr = nullptr);
keel::String symEvalSource(const numkit::Value &v);
numkit::Value symAssumptions(const numkit::Value &symVal,
                             keel::Allocator *mr = nullptr);
numkit::Value symDouble(const numkit::Value &v,
                        keel::Allocator *mr = nullptr);
numkit::Value symVpa(keel::ArrayRef<numkit::Value> args,
                     keel::Allocator *mr = nullptr);
numkit::Value symChar(const numkit::Value &v,
                      keel::Allocator *mr = nullptr);
numkit::Value symLatex(const numkit::Value &v,
                       keel::Allocator *mr = nullptr);
numkit::Value symCCode(const numkit::Value &v,
                       keel::Allocator *mr = nullptr);
numkit::Value symPretty(const numkit::Value &v,
                        keel::Allocator *mr = nullptr);
numkit::Value symSimplify(const numkit::Value &v,
                          keel::Allocator *mr = nullptr);
numkit::Value symExpand(const numkit::Value &v,
                        keel::Allocator *mr = nullptr);
void symFactor(keel::ArrayRef<numkit::Value> args, keel::usize nargout,
               keel::MutArrayRef<numkit::Value> outs,
               keel::Allocator *mr = nullptr);
numkit::Value symCollect(keel::ArrayRef<numkit::Value> args,
                         keel::Allocator *mr = nullptr);
void symCoeffs(keel::ArrayRef<numkit::Value> args, keel::usize nargout,
               keel::MutArrayRef<numkit::Value> outs,
               keel::Allocator *mr = nullptr);
void symNumden(const numkit::Value &v, keel::usize nargout,
               keel::MutArrayRef<numkit::Value> outs,
               keel::Allocator *mr = nullptr);
numkit::Value symPartfrac(keel::ArrayRef<numkit::Value> args,
                          keel::Allocator *mr = nullptr);
numkit::Value symSubs(keel::ArrayRef<numkit::Value> args,
                      keel::Allocator *mr = nullptr);
numkit::Value symSymvar(keel::ArrayRef<numkit::Value> args,
                        keel::Allocator *mr = nullptr);
numkit::Value symPoly2sym(keel::ArrayRef<numkit::Value> args,
                          keel::Allocator *mr = nullptr);
numkit::Value symSym2poly(keel::ArrayRef<numkit::Value> args,
                          keel::Allocator *mr = nullptr);
numkit::Value symDiff(keel::ArrayRef<numkit::Value> args,
                      keel::Allocator *mr = nullptr);
numkit::Value symInt(keel::ArrayRef<numkit::Value> args,
                     keel::Allocator *mr = nullptr);
numkit::Value symLimit(keel::ArrayRef<numkit::Value> args,
                       keel::Allocator *mr = nullptr);
numkit::Value symTaylor(keel::ArrayRef<numkit::Value> args,
                        keel::Allocator *mr = nullptr);
numkit::Value symLaurent(keel::ArrayRef<numkit::Value> args,
                         keel::Allocator *mr = nullptr);
numkit::Value symMtaylor(keel::ArrayRef<numkit::Value> args,
                         keel::Allocator *mr = nullptr);
void symPade(keel::ArrayRef<numkit::Value> args, keel::usize nargout,
             keel::MutArrayRef<numkit::Value> outs,
             keel::Allocator *mr = nullptr);
numkit::Value symResidue(keel::ArrayRef<numkit::Value> args,
                         keel::Allocator *mr = nullptr);
numkit::Value symSymsum(keel::ArrayRef<numkit::Value> args,
                        keel::Allocator *mr = nullptr);
numkit::Value symFiniteDiff(keel::ArrayRef<numkit::Value> args,
                            keel::Allocator *mr = nullptr);
numkit::Value symEulerMaclaurin(keel::ArrayRef<numkit::Value> args,
                                keel::Allocator *mr = nullptr);
void symSolve(keel::ArrayRef<numkit::Value> args, keel::usize nargout,
              keel::MutArrayRef<numkit::Value> outs,
              keel::Allocator *mr = nullptr);
numkit::Value symGroebner(keel::ArrayRef<numkit::Value> args,
                          keel::Allocator *mr = nullptr);
numkit::Value symPolyReduce(keel::ArrayRef<numkit::Value> args,
                            keel::Allocator *mr = nullptr);
numkit::Value symDsolve(keel::ArrayRef<numkit::Value> args,
                        keel::Allocator *mr = nullptr);
numkit::Value symPdsolve(keel::ArrayRef<numkit::Value> args,
                         keel::Allocator *mr = nullptr);
numkit::Value symLaplace(keel::ArrayRef<numkit::Value> args,
                         keel::Allocator *mr = nullptr);
numkit::Value symIlaplace(keel::ArrayRef<numkit::Value> args,
                          keel::Allocator *mr = nullptr);
numkit::Value symFourier(keel::ArrayRef<numkit::Value> args,
                         keel::Allocator *mr = nullptr);
numkit::Value symIfourier(keel::ArrayRef<numkit::Value> args,
                          keel::Allocator *mr = nullptr);
numkit::Value symZtrans(keel::ArrayRef<numkit::Value> args,
                        keel::Allocator *mr = nullptr);
numkit::Value symIztrans(keel::ArrayRef<numkit::Value> args,
                         keel::Allocator *mr = nullptr);
numkit::Value symRsolve(keel::ArrayRef<numkit::Value> args,
                        keel::Allocator *mr = nullptr);
numkit::Value symDet(const numkit::Value &A,
                     keel::Allocator *mr = nullptr);
numkit::Value symInv(const numkit::Value &A,
                     keel::Allocator *mr = nullptr);
numkit::Value symTrace(const numkit::Value &A,
                       keel::Allocator *mr = nullptr);
numkit::Value symAdjugate(const numkit::Value &A,
                          keel::Allocator *mr = nullptr);
numkit::Value symCharpoly(keel::ArrayRef<numkit::Value> args,
                          keel::Allocator *mr = nullptr);
numkit::Value symRank(const numkit::Value &A,
                      keel::Allocator *mr = nullptr);
void symRref(const numkit::Value &A, keel::usize nargout,
             keel::MutArrayRef<numkit::Value> outs,
             keel::Allocator *mr = nullptr);
numkit::Value symNull(const numkit::Value &A,
                      keel::Allocator *mr = nullptr);
numkit::Value symLinsolve(const numkit::Value &A, const numkit::Value &B,
                          keel::Allocator *mr = nullptr);
void symLu(const numkit::Value &A, keel::usize nargout,
           keel::MutArrayRef<numkit::Value> outs,
           keel::Allocator *mr = nullptr);
void symQr(const numkit::Value &A, keel::usize nargout,
           keel::MutArrayRef<numkit::Value> outs,
           keel::Allocator *mr = nullptr);
void symEig(const numkit::Value &A, keel::usize nargout,
            keel::MutArrayRef<numkit::Value> outs,
            keel::Allocator *mr = nullptr);
void symJordan(const numkit::Value &A, keel::usize nargout,
               keel::MutArrayRef<numkit::Value> outs,
               keel::Allocator *mr = nullptr);
numkit::Value symExpm(keel::ArrayRef<numkit::Value> args,
                      keel::Allocator *mr = nullptr);
numkit::Value symJacobian(keel::ArrayRef<numkit::Value> args,
                          keel::Allocator *mr = nullptr);
numkit::Value symGradient(keel::ArrayRef<numkit::Value> args,
                          keel::Allocator *mr = nullptr);
numkit::Value symHessian(keel::ArrayRef<numkit::Value> args,
                         keel::Allocator *mr = nullptr);
numkit::Value symDivergence(const numkit::Value &F, const numkit::Value &vars,
                            keel::Allocator *mr = nullptr);
numkit::Value symCurl(const numkit::Value &F, const numkit::Value &vars,
                      keel::Allocator *mr = nullptr);
numkit::Value symLaplacian(keel::ArrayRef<numkit::Value> args,
                           keel::Allocator *mr = nullptr);
numkit::Value symWronskian(keel::ArrayRef<numkit::Value> args,
                           keel::Allocator *mr = nullptr);
numkit::Value symPotential(const numkit::Value &F, const numkit::Value &vars,
                           keel::Allocator *mr = nullptr);
numkit::Value symEulerLagrange(keel::ArrayRef<numkit::Value> args,
                               keel::Allocator *mr = nullptr);
numkit::Value symHamiltonian(keel::ArrayRef<numkit::Value> args,
                             keel::Allocator *mr = nullptr);
numkit::Value symLegendreTransform(keel::ArrayRef<numkit::Value> args,
                                   keel::Allocator *mr = nullptr);
numkit::Value symPoissonBracket(keel::ArrayRef<numkit::Value> args,
                                keel::Allocator *mr = nullptr);
numkit::Value symLagrangeExtrema(keel::ArrayRef<numkit::Value> args,
                                 keel::Allocator *mr = nullptr);
numkit::Value symFrenetSerret(keel::ArrayRef<numkit::Value> args,
                              keel::Allocator *mr = nullptr);
numkit::Value symSurfaceCurvature(keel::ArrayRef<numkit::Value> args,
                                  keel::Allocator *mr = nullptr);
numkit::Value symChristoffel(const numkit::Value &metric, const numkit::Value &coords,
                             keel::Allocator *mr = nullptr);
numkit::Value symRiemann(const numkit::Value &metric, const numkit::Value &coords,
                         keel::Allocator *mr = nullptr);
numkit::Value symRicci(const numkit::Value &metric, const numkit::Value &coords,
                       keel::Allocator *mr = nullptr);
numkit::Value symScalarCurvature(const numkit::Value &metric, const numkit::Value &coords,
                                 keel::Allocator *mr = nullptr);
numkit::Value symGeodesic(keel::ArrayRef<numkit::Value> args,
                          keel::Allocator *mr = nullptr);
numkit::Value symLineIntegral(keel::ArrayRef<numkit::Value> args,
                              keel::Allocator *mr = nullptr);
numkit::Value symSurfaceIntegral(keel::ArrayRef<numkit::Value> args,
                                 keel::Allocator *mr = nullptr);
numkit::Value symElemFunc1(keel::StringRef fnName, const numkit::Value &v,
                           keel::Allocator *mr = nullptr);
numkit::Value symElemFunc2(keel::StringRef fnName, const numkit::Value &a,
                           const numkit::Value &b,
                           keel::Allocator *mr = nullptr);

} // namespace numkit::cas
