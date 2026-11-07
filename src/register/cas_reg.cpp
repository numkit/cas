// src/register/cas_reg.cpp — Registration hub for Symbolic Math Toolbox (numkit::cas).
#include <numkit/cas/library.hpp>
#include <numkit/cas/sym_value.hpp>
#include <numkit/sys/plugin.hpp>
#include <numkit/value/argcheck.hpp>

#include <string>
#include <utility>
#include <vector>

namespace numkit::cas::detail {

inline std::pmr::memory_resource *mrOf(const CallContext &ctx) noexcept
{
    return ctx.engine ? ctx.engine->resource() : nullptr;
}

void sym_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 0, 2, "sym");
    outs[0] = symCreate(args, mrOf(ctx));
}

void syms_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 64, "syms");
    std::vector<std::pair<std::string, Value>> bindings;
    symsCommand(args, bindings, mrOf(ctx));
    if (ctx.engine) {
        auto *pluginCtx = reinterpret_cast<PluginContext *>(ctx.engine);
        for (auto &kv : bindings) {
            pluginCtx->assignToCaller(0, kv.first, std::move(kv.second));
        }
    }
    if (!outs.empty()) {
        outs[0] = Value();
    }
}

void assume_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 2, 2, "assume");
    if (!(args[1].isChar() || args[1].isString())) {
        argcheck::detail::fail("assume: input 2 (domain) must be a string or character vector.", "assume", "numkit:assume:invalidDomain");
    }
    std::string dom = args[1].toString();
    outs[0] = symAssume(args[0], dom, mrOf(ctx));
}

void assumptions_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 1, "assumptions");
    outs[0] = symAssumptions(args[0], mrOf(ctx));
}

void vpa_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 2, "vpa");
    outs[0] = symVpa(args, mrOf(ctx));
}

void poly2sym_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 2, "poly2sym");
    outs[0] = symPoly2sym(args, mrOf(ctx));
}

void sym2poly_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 2, "sym2poly");
    outs[0] = symSym2poly(args, mrOf(ctx));
}

void symvar_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 2, "symvar");
    outs[0] = symSymvar(args, mrOf(ctx));
}

void simplify_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 1, "simplify");
    outs[0] = symSimplify(args[0], mrOf(ctx));
}

void expand_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 1, "expand");
    outs[0] = symExpand(args[0], mrOf(ctx));
}

void factor_reg(Span<const Value> args, size_t nargout, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 2, "factor");
    symFactor(args, nargout, outs, mrOf(ctx));
}

void collect_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 2, "collect");
    outs[0] = symCollect(args, mrOf(ctx));
}

void coeffs_reg(Span<const Value> args, size_t nargout, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 2, "coeffs");
    symCoeffs(args, nargout, outs, mrOf(ctx));
}

void numden_reg(Span<const Value> args, size_t nargout, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 1, "numden");
    symNumden(args[0], nargout, outs, mrOf(ctx));
}

void partfrac_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 2, "partfrac");
    outs[0] = symPartfrac(args, mrOf(ctx));
}

void subs_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 2, 3, "subs");
    outs[0] = symSubs(args, mrOf(ctx));
}

void int_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 4, "int");
    outs[0] = symInt(args, mrOf(ctx));
}

void limit_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 4, "limit");
    outs[0] = symLimit(args, mrOf(ctx));
}

void taylor_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 4, "taylor");
    outs[0] = symTaylor(args, mrOf(ctx));
}

void laurent_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 2, 5, "laurent");
    outs[0] = symLaurent(args, mrOf(ctx));
}

void mtaylor_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 2, 4, "mtaylor");
    outs[0] = symMtaylor(args, mrOf(ctx));
}

void pade_reg(Span<const Value> args, size_t nargout, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 3, 5, "pade");
    symPade(args, nargout, outs, mrOf(ctx));
}

void symsum_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 4, "symsum");
    outs[0] = symSymsum(args, mrOf(ctx));
}

void finitediff_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 3, "finitediff");
    outs[0] = symFiniteDiff(args, mrOf(ctx));
}

void eulermaclaurin_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 4, 5, "eulermaclaurin");
    outs[0] = symEulerMaclaurin(args, mrOf(ctx));
}

void solve_reg(Span<const Value> args, size_t nargout, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 2, "solve");
    symSolve(args, nargout, outs, mrOf(ctx));
}

void groebner_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 3, "groebner");
    outs[0] = symGroebner(args, mrOf(ctx));
}

void polyreduce_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 2, 4, "polyreduce");
    outs[0] = symPolyReduce(args, mrOf(ctx));
}

void dsolve_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 8, "dsolve");
    outs[0] = symDsolve(args, mrOf(ctx));
}

void pdsolve_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 4, 8, "pdsolve");
    outs[0] = symPdsolve(args, mrOf(ctx));
}

void laplace_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 3, "laplace");
    outs[0] = symLaplace(args, mrOf(ctx));
}

void ilaplace_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 3, "ilaplace");
    outs[0] = symIlaplace(args, mrOf(ctx));
}

void fourier_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 3, "fourier");
    outs[0] = symFourier(args, mrOf(ctx));
}

void ifourier_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 3, "ifourier");
    outs[0] = symIfourier(args, mrOf(ctx));
}

void ztrans_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 3, "ztrans");
    outs[0] = symZtrans(args, mrOf(ctx));
}

void iztrans_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 3, "iztrans");
    outs[0] = symIztrans(args, mrOf(ctx));
}

void rsolve_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 2, 4, "rsolve");
    outs[0] = symRsolve(args, mrOf(ctx));
}

void latex_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 1, "latex");
    outs[0] = symLatex(args[0], mrOf(ctx));
}

void ccode_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 1, "ccode");
    outs[0] = symCCode(args[0], mrOf(ctx));
}

void charpoly_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 2, "charpoly");
    outs[0] = symCharpoly(args, mrOf(ctx));
}

void adjugate_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 1, "adjugate");
    outs[0] = symAdjugate(args[0], mrOf(ctx));
}

void jordan_reg(Span<const Value> args, size_t nargout, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 1, "jordan");
    symJordan(args[0], nargout, outs, mrOf(ctx));
}

void jacobian_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 2, "jacobian");
    outs[0] = symJacobian(args, mrOf(ctx));
}

void gradient_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 2, "gradient");
    outs[0] = symGradient(args, mrOf(ctx));
}

void hessian_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 2, "hessian");
    outs[0] = symHessian(args, mrOf(ctx));
}

void divergence_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 2, 2, "divergence");
    outs[0] = symDivergence(args[0], args[1], mrOf(ctx));
}

void curl_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 2, 2, "curl");
    outs[0] = symCurl(args[0], args[1], mrOf(ctx));
}

void laplacian_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 2, "laplacian");
    outs[0] = symLaplacian(args, mrOf(ctx));
}

void wronskian_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 2, "wronskian");
    outs[0] = symWronskian(args, mrOf(ctx));
}

void potential_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 2, 2, "potential");
    outs[0] = symPotential(args[0], args[1], mrOf(ctx));
}

void eulerlagrange_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 4, 4, "eulerlagrange");
    outs[0] = symEulerLagrange(args, mrOf(ctx));
}

void hamiltonian_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 3, 3, "hamiltonian");
    outs[0] = symHamiltonian(args, mrOf(ctx));
}

void legendretransform_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 3, 3, "legendretransform");
    outs[0] = symLegendreTransform(args, mrOf(ctx));
}

void poissonbracket_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 4, 4, "poissonbracket");
    outs[0] = symPoissonBracket(args, mrOf(ctx));
}

void lagrangeextrema_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 3, 3, "lagrangeextrema");
    outs[0] = symLagrangeExtrema(args, mrOf(ctx));
}

void frenetserret_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 2, 2, "frenetserret");
    outs[0] = symFrenetSerret(args, mrOf(ctx));
}

void surfacecurvature_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 3, 3, "surfacecurvature");
    outs[0] = symSurfaceCurvature(args, mrOf(ctx));
}

void christoffel_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 2, 2, "christoffel");
    outs[0] = symChristoffel(args[0], args[1], mrOf(ctx));
}

void riemann_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 2, 2, "riemann");
    outs[0] = symRiemann(args[0], args[1], mrOf(ctx));
}

void ricci_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 2, 2, "ricci");
    outs[0] = symRicci(args[0], args[1], mrOf(ctx));
}

void scalarcurvature_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 2, 2, "scalarcurvature");
    outs[0] = symScalarCurvature(args[0], args[1], mrOf(ctx));
}

void geodesic_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 4, 4, "geodesic");
    outs[0] = symGeodesic(args, mrOf(ctx));
}

void lineintegral_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 5, 5, "lineintegral");
    outs[0] = symLineIntegral(args, mrOf(ctx));
}

void surfaceintegral_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 8, 8, "surfaceintegral");
    outs[0] = symSurfaceIntegral(args, mrOf(ctx));
}

void airyAi_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 1, "airyAi");
    outs[0] = symElemFunc1("airyAi", args[0], mrOf(ctx));
}

void airyBi_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 1, "airyBi");
    outs[0] = symElemFunc1("airyBi", args[0], mrOf(ctx));
}

void legendreP_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 2, 2, "legendreP");
    outs[0] = symElemFunc2("legendreP", args[0], args[1], mrOf(ctx));
}

void chebyshevT_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 2, 2, "chebyshevT");
    outs[0] = symElemFunc2("chebyshevT", args[0], args[1], mrOf(ctx));
}

void chebyshevU_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 2, 2, "chebyshevU");
    outs[0] = symElemFunc2("chebyshevU", args[0], args[1], mrOf(ctx));
}

void hermiteH_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 2, 2, "hermiteH");
    outs[0] = symElemFunc2("hermiteH", args[0], args[1], mrOf(ctx));
}

void laguerreL_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 2, 2, "laguerreL");
    outs[0] = symElemFunc2("laguerreL", args[0], args[1], mrOf(ctx));
}

void heaviside_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 1, "heaviside");
    outs[0] = symElemFunc1("heaviside", args[0], mrOf(ctx));
}

void dirac_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 1, "dirac");
    outs[0] = symElemFunc1("dirac", args[0], mrOf(ctx));
}

void zeta_reg(Span<const Value> args, size_t /*nargout*/, Span<Value> outs, CallContext &ctx)
{
    argcheck::checkNargin(args.size(), 1, 1, "zeta");
    outs[0] = symElemFunc1("zeta", args[0], mrOf(ctx));
}

} // namespace numkit::cas::detail

namespace numkit {

void CasLibrary::install(PluginContext &engine)
{
    engine.registerClass(cas::makeSymBuiltinClass());

    engine.registerFunction("cas", "sym", &cas::detail::sym_reg);
    engine.registerFunction("cas", "syms", &cas::detail::syms_reg);
    engine.registerFunction("cas", "assume", &cas::detail::assume_reg);
    engine.registerFunction("cas", "assumptions", &cas::detail::assumptions_reg);
    engine.registerFunction("cas", "vpa", &cas::detail::vpa_reg);
    engine.registerFunction("cas", "poly2sym", &cas::detail::poly2sym_reg);
    engine.registerFunction("cas", "sym2poly", &cas::detail::sym2poly_reg);
    engine.registerFunction("cas", "symvar", &cas::detail::symvar_reg);
    engine.registerFunction("cas", "simplify", &cas::detail::simplify_reg);
    engine.registerFunction("cas", "expand", &cas::detail::expand_reg);
    engine.registerFunction("cas", "factor", &cas::detail::factor_reg);
    engine.registerFunction("cas", "collect", &cas::detail::collect_reg);
    engine.registerFunction("cas", "coeffs", &cas::detail::coeffs_reg);
    engine.registerFunction("cas", "numden", &cas::detail::numden_reg);
    engine.registerFunction("cas", "partfrac", &cas::detail::partfrac_reg);
    engine.registerFunction("cas", "subs", &cas::detail::subs_reg);
    engine.registerFunction("cas", "int", &cas::detail::int_reg);
    engine.registerFunction("cas", "defint", &cas::detail::int_reg);
    engine.registerFunction("cas", "limit", &cas::detail::limit_reg);
    engine.registerFunction("cas", "taylor", &cas::detail::taylor_reg);
    engine.registerFunction("cas", "laurent", &cas::detail::laurent_reg);
    engine.registerFunction("cas", "mtaylor", &cas::detail::mtaylor_reg);
    engine.registerFunction("cas", "pade", &cas::detail::pade_reg);
    engine.registerFunction("cas", "symsum", &cas::detail::symsum_reg);
    engine.registerFunction("cas", "finitediff", &cas::detail::finitediff_reg);
    engine.registerFunction("cas", "eulermaclaurin", &cas::detail::eulermaclaurin_reg);
    engine.registerFunction("cas", "solve", &cas::detail::solve_reg);
    engine.registerFunction("cas", "groebner", &cas::detail::groebner_reg);
    engine.registerFunction("cas", "polyreduce", &cas::detail::polyreduce_reg);
    engine.registerFunction("cas", "dsolve", &cas::detail::dsolve_reg);
    engine.registerFunction("cas", "pdsolve", &cas::detail::pdsolve_reg);
    engine.registerFunction("cas", "laplace", &cas::detail::laplace_reg);
    engine.registerFunction("cas", "ilaplace", &cas::detail::ilaplace_reg);
    engine.registerFunction("cas", "fourier", &cas::detail::fourier_reg);
    engine.registerFunction("cas", "ifourier", &cas::detail::ifourier_reg);
    engine.registerFunction("cas", "ztrans", &cas::detail::ztrans_reg);
    engine.registerFunction("cas", "iztrans", &cas::detail::iztrans_reg);
    engine.registerFunction("cas", "rsolve", &cas::detail::rsolve_reg);
    engine.registerFunction("cas", "latex", &cas::detail::latex_reg);
    engine.registerFunction("cas", "ccode", &cas::detail::ccode_reg);
    engine.registerFunction("cas", "charpoly", &cas::detail::charpoly_reg);
    engine.registerFunction("cas", "adjugate", &cas::detail::adjugate_reg);
    engine.registerFunction("cas", "jordan", &cas::detail::jordan_reg);
    engine.registerFunction("cas", "jacobian", &cas::detail::jacobian_reg);
    engine.registerFunction("cas", "gradient", &cas::detail::gradient_reg);
    engine.registerFunction("cas", "hessian", &cas::detail::hessian_reg);
    engine.registerFunction("cas", "divergence", &cas::detail::divergence_reg);
    engine.registerFunction("cas", "curl", &cas::detail::curl_reg);
    engine.registerFunction("cas", "laplacian", &cas::detail::laplacian_reg);
    engine.registerFunction("cas", "wronskian", &cas::detail::wronskian_reg);
    engine.registerFunction("cas", "potential", &cas::detail::potential_reg);
    engine.registerFunction("cas", "eulerlagrange", &cas::detail::eulerlagrange_reg);
    engine.registerFunction("cas", "hamiltonian", &cas::detail::hamiltonian_reg);
    engine.registerFunction("cas", "legendretransform", &cas::detail::legendretransform_reg);
    engine.registerFunction("cas", "poissonbracket", &cas::detail::poissonbracket_reg);
    engine.registerFunction("cas", "lagrangeextrema", &cas::detail::lagrangeextrema_reg);
    engine.registerFunction("cas", "frenetserret", &cas::detail::frenetserret_reg);
    engine.registerFunction("cas", "surfacecurvature", &cas::detail::surfacecurvature_reg);
    engine.registerFunction("cas", "christoffel", &cas::detail::christoffel_reg);
    engine.registerFunction("cas", "riemann", &cas::detail::riemann_reg);
    engine.registerFunction("cas", "ricci", &cas::detail::ricci_reg);
    engine.registerFunction("cas", "scalarcurvature", &cas::detail::scalarcurvature_reg);
    engine.registerFunction("cas", "geodesic", &cas::detail::geodesic_reg);
    engine.registerFunction("cas", "lineintegral", &cas::detail::lineintegral_reg);
    engine.registerFunction("cas", "surfaceintegral", &cas::detail::surfaceintegral_reg);
    engine.registerFunction("cas", "airyAi", &cas::detail::airyAi_reg);
    engine.registerFunction("cas", "airyBi", &cas::detail::airyBi_reg);
    engine.registerFunction("cas", "legendreP", &cas::detail::legendreP_reg);
    engine.registerFunction("cas", "chebyshevT", &cas::detail::chebyshevT_reg);
    engine.registerFunction("cas", "chebyshevU", &cas::detail::chebyshevU_reg);
    engine.registerFunction("cas", "hermiteH", &cas::detail::hermiteH_reg);
    engine.registerFunction("cas", "laguerreL", &cas::detail::laguerreL_reg);
    engine.registerFunction("cas", "heaviside", &cas::detail::heaviside_reg);
    engine.registerFunction("cas", "dirac", &cas::detail::dirac_reg);
    engine.registerFunction("cas", "zeta", &cas::detail::zeta_reg);
}

} // namespace numkit
