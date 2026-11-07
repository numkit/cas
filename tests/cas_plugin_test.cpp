// tests/cas_plugin_test.cpp — Dual-engine (TreeWalker + Bytecode VM) integration tests
// for the Symbolic Math Toolbox (numkit::cas) plugin and `sym` object class.

#include <numkit/core/standard_engine.hpp>
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
        std::string sTw = tw.eval(expr).toString();
        std::string sVm = vm.eval(expr).toString();
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
    expectScalar("double(subs(exp(x) + log(x), x, 1))", std::exp(1.0), 1e-12);
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
