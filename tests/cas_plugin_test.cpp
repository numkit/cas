// tests/cas_plugin_test.cpp — Dual-engine (TreeWalker + Bytecode VM) integration tests
// for the Symbolic Math Toolbox (numkit::cas) plugin and `sym` object class.

#include <numkit/core/standard_engine.hpp>
#include <keel/math.h>
#include <numkit/core/engine.hpp>
#include <gtest/gtest.h>

#include <cmath>
#include <string>

using namespace numkit;

class CasPluginTest : public ::testing::Test
{
public:
    StandardEngine tw;
    StandardEngine vm;

    void SetUp() override
    {
        tw.setBackend(Engine::Backend::TreeWalker);
        vm.setBackend(Engine::Backend::VM);
    }

    void evalBoth(const std::string &code)
    {
        tw.eval(code);
        vm.eval(code);
    }

    void expectScalar(const std::string &expr, double expected, double tol = 1e-10)
    {
        double vTw = tw.eval(expr).toScalar();
        double vVm = vm.eval(expr).toScalar();
        EXPECT_NEAR(vTw, expected, tol) << "TreeWalker failed on: " << expr;
        EXPECT_NEAR(vVm, expected, tol) << "Bytecode VM failed on: " << expr;
    }

    void expectString(const std::string &expr, const std::string &expected)
    {
        std::string sTw(tw.eval(expr).toString().as_ref());
        std::string sVm(vm.eval(expr).toString().as_ref());
        EXPECT_EQ(sTw, expected) << "TreeWalker failed on: " << expr;
        EXPECT_EQ(sVm, expected) << "Bytecode VM failed on: " << expr;
    }

    void expectSymEqual(const std::string &lhsExpr, const std::string &rhsExpr)
    {
        std::string check = "double(simplify((" + lhsExpr + ") - (" + rhsExpr + ")))";
        expectScalar(check, 0.0, 1e-12);
    }

    void expectThrowsBoth(const std::string &code)
    {
        EXPECT_THROW(tw.eval(code), std::exception) << "TreeWalker did not throw on: " << code;
        EXPECT_THROW(vm.eval(code), std::exception) << "Bytecode VM did not throw on: " << code;
    }
};

TEST_F(CasPluginTest, SymCreationAndSymsCommand)
{
    evalBoth("x = sym('x'); y = sym('y', 'positive');");
    expectString("class(x)", "sym");
    expectString("char(x)", "x");
    expectString("assumptions(y)", "positive");

    // Command-form `syms a b c real` in both TreeWalker and Bytecode VM
    evalBoth("syms a b c real");
    expectString("class(a)", "sym");
    expectString("assumptions(a)", "real");
    expectSymEqual("(a + b) - a", "b");

    // Rational exact constructor
    evalBoth("q = sym(1.5);");
    expectString("char(q)", "3/2");
    expectScalar("double(q)", 1.5);
}

TEST_F(CasPluginTest, SymbolicArithmeticAndElementaryFunctions)
{
    evalBoth("syms x y");
    expectSymEqual("(x + y)^2 - (x^2 + 2*x*y + y^2)", "0");
    expectSymEqual("sin(x)^2 + cos(x)^2", "1");
    expectScalar("double(subs(exp(x) + log(x), x, 1))", keel::exp(1.0), 1e-12);
    expectScalar("double(vpa(sym('pi'), 15))", 3.141592653589793, 1e-12);
}

TEST_F(CasPluginTest, AlgebraicSimplificationAndPolynomialTools)
{
    evalBoth("syms x y");
    expectSymEqual("expand((x + 1)*(x - 1))", "x^2 - 1");
    expectSymEqual("simplify((x^2 - 1)/(x - 1))", "x + 1");
    expectSymEqual("collect(x^2 + 2*x*y + x + y, x)", "(1 + 2*y)*x + x^2 + y");

    evalBoth("[N, D] = numden(1/x + 1/y);");
    expectSymEqual("N / D", "1/x + 1/y");

    evalBoth("pf = partfrac(1 / (x^2 - 1), x);");
    expectSymEqual("pf", "1/(2*(x - 1)) - 1/(2*(x + 1))");

    evalBoth("p = poly2sym([1, 0, -2], x);");
    expectSymEqual("p", "x^2 - 2");
    evalBoth("c = sym2poly(x^3 - 2*x + 5, x);");
    expectScalar("c(1)", 1.0);
    expectScalar("c(2)", 0.0);
    expectScalar("c(3)", -2.0);
    expectScalar("c(4)", 5.0);

    evalBoth("[cf, tm] = coeffs(3*x^2 + 5*x + 7, x);");
    expectScalar("double(cf(1))", 7.0);
    expectScalar("double(cf(2))", 5.0);
    expectScalar("double(cf(3))", 3.0);
}

TEST_F(CasPluginTest, CalculusDiffIntLimitTaylorSymsum)
{
    evalBoth("syms x n");
    expectSymEqual("diff(sin(x^2), x)", "2*x*cos(x^2)");
    expectSymEqual("diff(x^4, x, 2)", "12*x^2");

    // Indefinite and definite integration
    expectSymEqual("diff(int(x^2 * exp(x), x), x)", "x^2 * exp(x)");
    expectScalar("double(int(x^2, x, 0, 3))", 9.0, 1e-12);
    expectScalar("double(int(sin(x), x, 0, sym('pi')))", 2.0, 1e-12);

    // Limits
    expectScalar("double(limit(sin(x)/x, x, 0))", 1.0, 1e-12);
    expectScalar("double(limit((1 - cos(x))/x^2, x, 0))", 0.5, 1e-12);

    // Taylor, Laurent, Pade
    expectSymEqual("taylor(exp(x), x, 0, 3)", "1 + x + x^2/2 + x^3/6");
    evalBoth("[P, Q] = pade(exp(x), x, 0, 1, 1);");
    expectSymEqual("P / Q", "(1 + x/2) / (1 - x/2)");

    // Symbolic summation (Gosper / polynomial)
    expectSymEqual("symsum(n, n, 1, x)", "x*(x + 1)/2");
}

TEST_F(CasPluginTest, SymbolicMatricesAndLinearAlgebra)
{
    evalBoth("syms a b c d x");
    // Mixed symbolic + numeric concatenation and indexing
    evalBoth("A = [a, 1; 2, b];");
    expectScalar("size(A, 1)", 2.0);
    expectScalar("size(A, 2)", 2.0);
    expectSymEqual("A(1, 1)", "a");
    expectSymEqual("A(1, 2)", "1");
    expectSymEqual("A(2, 1)", "2");
    expectSymEqual("A(2, 2)", "b");

    // Slice assignment with numeric promotion
    evalBoth("B = A; B(1, 2) = 3;");
    expectSymEqual("det(B)", "a*b - 6");
    expectSymEqual("trace(B)", "a + b");

    // Inverse and linear solve
    evalBoth("M = [sym(2), sym(1); sym(1), sym(2)];");
    evalBoth("Minv = inv(M);");
    expectScalar("double(Minv(1, 1))", 2.0 / 3.0);
    expectScalar("double(Minv(1, 2))", -1.0 / 3.0);

    evalBoth("rhs = [x; sym(1)]; sol = M \\ rhs;");
    expectSymEqual("sol(1)", "(2*x - 1)/3");
    expectSymEqual("sol(2)", "(2 - x)/3");

    // LU, QR, RREF, Nullspace, Eigenvalues, Jordan, Expm, Charpoly
    evalBoth("[L, U, P] = lu(M);");
    expectScalar("double(det(P*M - L*U))", 0.0);

    evalBoth("[V, D] = eig(M);");
    expectScalar("double(D(1, 1) + D(2, 2))", 4.0);
    expectScalar("double(D(1, 1) * D(2, 2))", 3.0);

    evalBoth("[Vj, J] = jordan([sym(2), sym(1); sym(0), sym(2)]);");
    expectScalar("double(J(1, 1))", 2.0);
    expectScalar("double(J(1, 2))", 1.0);

    evalBoth("cp = charpoly(M, x);");
    expectSymEqual("cp", "x^2 - 4*x + 3");
}

TEST_F(CasPluginTest, EquationAndDifferentialSolvers)
{
    evalBoth("syms x y t");
    evalBoth("roots_x = solve(x^2 - 5*x + 6, x);");
    expectScalar("double(roots_x(1) + roots_x(2))", 5.0);
    expectScalar("double(roots_x(1) * roots_x(2))", 6.0);

    // Multivariate linear/polynomial system
    evalBoth("[sx, sy] = solve([x + y - 5, x - y - 1], [x, y]);");
    expectScalar("double(sx(1))", 3.0);
    expectScalar("double(sy(1))", 2.0);

    // ODE solver: y'(t) + 2*y(t) = 0, y(0) = 3 => 3*exp(-2*t)
    evalBoth("y_sol = dsolve([2, 1], 0, t, 0, 3);");
    expectSymEqual("y_sol", "3*exp(-2*t)");

    // Recurrence solver: a(n+1) - 2*a(n) = 0, a(0) = 5 => 5*2^n
    evalBoth("syms n; a_sol = rsolve([-2, 1], 0, n, 5);");
    expectScalar("double(subs(a_sol, n, 4))", 80.0);
}

TEST_F(CasPluginTest, IntegralTransforms)
{
    evalBoth("syms t s w n z");
    expectSymEqual("laplace(exp(-2*t), t, s)", "1/(s + 2)");
    expectSymEqual("ilaplace(1/(s + 2), s, t)", "exp(-2*t)");
    expectSymEqual("ztrans(sym(1), n, z)", "z/(z - 1)");
    expectSymEqual("iztrans(z/(z - 1), z, n)", "1");
}

TEST_F(CasPluginTest, VectorCalculusAndDifferentialGeometry)
{
    evalBoth("syms x y z");
    evalBoth("f = x^2 + y^2 + z^2; vars = [x, y, z];");
    evalBoth("g = gradient(f, vars);");
    expectSymEqual("g(1)", "2*x");
    expectSymEqual("g(2)", "2*y");
    expectSymEqual("g(3)", "2*z");
    expectSymEqual("laplacian(f, vars)", "6");

    evalBoth("F = [x*y, y*z, z*x];");
    expectSymEqual("divergence(F, vars)", "x + y + z");
    evalBoth("C = curl(g, vars);");
    expectScalar("double(C(1))", 0.0);
    expectScalar("double(C(2))", 0.0);
    expectScalar("double(C(3))", 0.0);

    evalBoth("P = potential(g, vars);");
    expectSymEqual("P", "x^2 + y^2 + z^2");

    // 2-sphere metric in (x=theta, y=phi): diag(1, sin(x)^2) => Gaussian/scalar curvature
    evalBoth("G = [sym(1), sym(0); sym(0), sin(x)^2];");
    expectSymEqual("scalarcurvature(G, [x, y])", "2");
}

TEST_F(CasPluginTest, CodeGenerationAndValidationErrors)
{
    evalBoth("syms x");
    expectString("latex(x^2 + 1)", "1 + x^{2}");
    expectString("ccode(x + 1)", "1.0 + x");

    // Argcheck validation errors
    expectThrowsBoth("sym(1, 2, 3)");
    expectThrowsBoth("assume(x, 'invalid_domain')");
    expectThrowsBoth("divergence([x, y], [x, y])");
}

TEST_F(CasPluginTest, FieldtestRegressionsRelationalSymfunDsolveIlaplaceSolveComplexPretty)
{
    // 1. Symbolic relational operators return sym (not logical) + lhs/rhs/isAlways
    evalBoth("syms x y s t");
    evalBoth("eq1 = (x^2 == 4);");
    expectString("class(eq1)", "sym");
    expectString("char(eq1)", "x^2 == 4");
    expectSymEqual("lhs(eq1)", "x^2");
    expectSymEqual("rhs(eq1)", "4");
    expectScalar("double(isAlways(sym(2) == sym(2)))", 1.0);
    expectScalar("double(isAlways(sym(2) < sym(3)))", 1.0);

    // 2. Complex numeric * sym arithmetic
    evalBoth("zc = 1i * x;");
    expectString("class(zc)", "sym");
    evalBoth("zc_val = double(subs(zc, x, 3));");
    expectScalar("real(zc_val)", 0.0);
    expectScalar("imag(zc_val)", 3.0);

    // 3. Variadic solve(eq1, eq2, [x y]) and solve(eq1, eq2, x, y) + == equations
    evalBoth("[sx1, sy1] = solve(x + y - 3, x - y - 1, [x y]);");
    expectScalar("double(sx1)", 2.0);
    expectScalar("double(sy1)", 1.0);
    evalBoth("s_struct = solve(x + y == 3, x - y == 1, [x y]);");
    expectScalar("double(s_struct.x)", 2.0);
    expectScalar("double(s_struct.y)", 1.0);
    evalBoth("[sx2, sy2] = solve(x + y == 3, x - y == 1, x, y);");
    expectScalar("double(sx2)", 2.0);
    expectScalar("double(sy2)", 1.0);

    // 4. Classic string dsolve (1st-order linear + comma-separated ICs)
    evalBoth("yd1 = dsolve('Dy = -5*y', 'y(0)=1', 't');");
    expectSymEqual("yd1", "exp(-5*t)");
    evalBoth("yd2 = dsolve('D2y = -sin(t)', 'y(0)=0, Dy(0)=0', 't');");
    expectSymEqual("yd2", "sin(t) - t");

    // 5. ilaplace time-shift exponential factor
    evalBoth("fl = ilaplace(exp(-2*s) / (s*(s + 1)), s, t);");
    expectScalar("double(subs(fl, t, 5))", 1.0 - keel::exp(-3.0), 1e-10);

    // 6. symfun: syms yf(t), f(x) = x^2 + 1, symbolic dsolve with diff(yf, t) == ...
    evalBoth("syms yf(t)");
    expectString("class(yf)", "symfun");
    expectScalar("double(isa(yf, 'sym'))", 1.0);
    expectString("char(yf)", "yf(t)");
    evalBoth("f(x) = x^2 + 1;");
    expectString("class(f)", "symfun");
    expectScalar("double(f(3))", 10.0);
    evalBoth("sol_sf1 = dsolve(diff(yf, t) == -5*yf, yf(0) == 1);");
    expectSymEqual("sol_sf1", "exp(-5*t)");
    evalBoth("Dyf = diff(yf, t);");
    evalBoth("sol_sf2 = dsolve(diff(yf, t, 2) == -sin(t), [yf(0) == 0, Dyf(0) == 0]);");
    expectSymEqual("sol_sf2", "sin(t) - t");

    // 7. pretty and matlabFunction
    evalBoth("pretty(x^2 + 1);");
    evalBoth("ps = pretty(x^2 + 1);");
    expectString("ps", "1 + x^2");
    evalBoth("fh = matlabFunction(sol_sf1);");
    expectScalar("fh(0)", 1.0, 1e-12);
    expectScalar("fh(1)", keel::exp(-5.0), 1e-12);
    evalBoth("fh2 = matlabFunction(x^2 + y, 'Vars', [x, y]);");
    expectScalar("fh2(3, 4)", 13.0, 1e-12);

    // 8. eval(sym) scalar/matrix, subs scalar-old/vector-new broadcast, vectorize,
    //    1-arg relational assume, and Laplace ODE with diff(y(t), t, 2) + subs
    evalBoth("a_num = 3; b_num = 4; syms a_num_s b_num_s;");
    evalBoth("ev_s = eval(sym(5) + sym(2));");
    expectScalar("ev_s", 7.0);
    evalBoth("ev_m = eval([sym(1) sym(2); sym(3) sym(4)]);");
    expectScalar("ev_m(2, 1)", 3.0);
    evalBoth("sub_v = double(subs(x^2 + 1, x, [1 2 3]));");
    expectScalar("sub_v(1)", 2.0);
    expectScalar("sub_v(3)", 10.0);
    expectString("vectorize(x^2 * y)", "y.*x.^2");
    evalBoth("syms tl sl Yl yl(tl); assume([tl, Yl] > 0);");
    evalBoth("Dyl = diff(yl, tl); D2yl = diff(yl, tl, 2);");
    evalBoth("LT = laplace(D2yl + Dyl == sin(tl), tl, sl);");
    evalBoth("LT = subs(LT, laplace(yl(tl), tl, sl), Yl);");
    evalBoth("LT = subs(LT, yl(0), 1);");
    evalBoth("LT = subs(LT, subs(diff(yl(tl), tl), tl, 0), 2);");
    evalBoth("Ysol = solve(LT, Yl);");
    evalBoth("Lsol = ilaplace(Ysol, sl, tl);");
    evalBoth("Dsol = dsolve(D2yl + Dyl == sin(tl), [yl(0) == 1, Dyl(0) == 2]);");
    expectScalar("double(subs(Lsol - Dsol, tl, 1.5))", 0.0, 1e-9);

    // 9. evalc capture and simultaneous multi-variable subs
    evalBoth("cap_s = evalc('disp(42)');");
    expectScalar("double(~isempty(strfind(cap_s, '42')))", 1.0);
    expectSymEqual("subs(x + 2*y, [x, y], [y, 3])", "y + 6");
    expectSymEqual("subs(x - y, [x, y], [y, x])", "y - x");

    // 10. Small-magnitude double->sym rational conversion (1.82e-10 must not truncate to 0)
    expectScalar("double(sym(1.82e-10))", 1.82e-10, 1e-22);
    evalBoth("syms Ag Cl; sol_ci = solve([Ag*Cl == 1.82e-10, Cl == Ag + 1e-5], [Ag, Cl]);");
    evalBoth("ag_v = double(sol_ci.Ag); ag_pos = ag_v(ag_v > 0);");
    expectScalar("ag_pos(1)", 0.5 * (-1e-5 + std::sqrt(1e-10 + 4.0 * 1.82e-10)), 1e-15);

    // 11. Variadic partial diff(f, x, x, y, y, y) and diff(f, x, 2, y, 3)
    expectSymEqual("diff(3*x^5*y^10, x, x, y, y, y)", "43200*x^3*y^7");
    expectSymEqual("diff(3*x^5*y^10, x, 2, y, 3)", "43200*x^3*y^7");

    // 12. vpa preserves free symbolic variables while evaluating constant subexpressions
    evalBoth("vp_expr = vpa(sym(1)/3 * exp(-sym(3)/2 * t));");
    expectScalar("double(subs(vp_expr, t, 2))", (1.0 / 3.0) * std::exp(-3.0), 1e-11);

    // 13. solve(..., 'Real', true) filters non-real roots without treating 'Real' as a variable
    evalBoth("r_real = solve(x^3 - 1 == 0, x, 'Real', true);");
    expectScalar("numel(r_real)", 1.0);
    expectScalar("double(r_real(1))", 1.0, 1e-12);

    // 14. Symbolic relational logical-mask indexing (e.g. sol.L(sol.L > 0))
    evalBoth("sv_mix = [sym(-5); sym(1000)/3; sym(0); sym(7)]; sv_pos = sv_mix(sv_mix > 0);");
    expectScalar("numel(sv_pos)", 2.0);
    expectScalar("double(sv_pos(1))", 1000.0 / 3.0, 1e-12);
    expectScalar("double(sv_pos(2))", 7.0, 1e-12);

    // 15. Divergent improper definite integral int(1/x, x, 0, inf) -> Inf (not error)
    evalBoth("div_i = int(1/x, x, 0, inf);");
    expectScalar("double(isinf(double(div_i)))", 1.0);
}
