#include <numkit/cas/core/parser.hpp>
#include <numkit/cas/linalg/symmatrix.hpp>

#include <gtest/gtest.h>

#include <cstdint>
#include <random>
#include <string>
#include <vector>

namespace numkit::cas {
namespace {

bool exprEq(Ctx &c, Expr a, Expr b)
{
    if (a.isNull() || b.isNull())
        return a.isNull() && b.isNull();
    const Expr diff = simplifyRationalExpr(c, c.add({a, c.neg(b)}));
    return !diff.isNull() && c.isZero(diff);
}

bool matEq(Ctx &c, const SymMatrix &A, const SymMatrix &B)
{
    if (A.rows() != B.rows() || A.cols() != B.cols())
        return false;
    for (std::size_t r = 0; r < A.rows(); ++r)
        for (std::size_t col = 0; col < A.cols(); ++col)
            if (!exprEq(c, A.at(r, col), B.at(r, col)))
                return false;
    return true;
}

SymMatrix parseMat(Ctx &c, std::size_t rows, std::size_t cols,
                   const std::vector<const char *> &src)
{
    std::vector<Expr> data;
    data.reserve(src.size());
    for (const char *s : src)
        data.push_back(parseExpr(c, s));
    return SymMatrix(rows, cols, std::move(data));
}

// ============================================================================
// Layer 1: Fixed Oracle Vectors
// ============================================================================

TEST(SymMatrixTest, BasicMatrixAlgebra)
{
    Ctx c;
    const SymMatrix A = parseMat(c, 2, 2, {"x", "1", "2", "x + 1"});
    const SymMatrix B = parseMat(c, 2, 2, {"1", "-1", "0", "x"});

    const SymMatrix sum = A.add(c, B);
    EXPECT_TRUE(matEq(c, sum, parseMat(c, 2, 2, {"x + 1", "0", "2", "2*x + 1"})));

    const SymMatrix diff = A.sub(c, B);
    EXPECT_TRUE(matEq(c, diff, parseMat(c, 2, 2, {"x - 1", "2", "2", "1"})));

    const SymMatrix prod = A.mul(c, B);
    EXPECT_TRUE(matEq(c, prod,
                      parseMat(c, 2, 2, {"x", "0", "2", "x^2 + x - 2"})));

    const SymMatrix AT = A.transpose();
    EXPECT_TRUE(matEq(c, AT, parseMat(c, 2, 2, {"x", "2", "1", "x + 1"})));

    EXPECT_TRUE(exprEq(c, A.trace(c), parseExpr(c, "2*x + 1")));
}

TEST(SymMatrixTest, JacobianPolarAnd3D)
{
    Ctx c;
    const Expr r = c.symbol("r");
    const Expr th = c.symbol("th");
    const std::vector<Expr> polar = {
        parseExpr(c, "r*cos(th)"),
        parseExpr(c, "r*sin(th)"),
    };
    const SymMatrix J = jacobian(c, polar, {r, th});
    ASSERT_EQ(J.rows(), 2u);
    ASSERT_EQ(J.cols(), 2u);
    EXPECT_TRUE(matEq(
        c, J,
        parseMat(c, 2, 2, {"cos(th)", "-r*sin(th)", "sin(th)", "r*cos(th)"})));

    // det(J) = r*(cos(th)^2 + sin(th)^2)
    const Expr detJ = det(c, J);
    EXPECT_TRUE(exprEq(c, detJ, parseExpr(c, "r*cos(th)^2 + r*sin(th)^2")));

    // 3D nonlinear map
    const Expr x = c.symbol("x");
    const Expr y = c.symbol("y");
    const Expr z = c.symbol("z");
    const std::vector<Expr> f3 = {
        parseExpr(c, "x^2*y"),
        parseExpr(c, "5*x + sin(y)"),
        parseExpr(c, "x*y*z"),
    };
    const SymMatrix J3 = jacobian(c, f3, {x, y, z});
    const SymMatrix wantJ3 = parseMat(c, 3, 3, {
        "2*x*y", "x^2",    "0",
        "5",     "cos(y)", "0",
        "y*z",   "x*z",    "x*y"
    });
    EXPECT_TRUE(matEq(c, J3, wantJ3));
}

TEST(SymMatrixTest, GradientAndHessianRosenbrock)
{
    Ctx c;
    const Expr x = c.symbol("x");
    const Expr y = c.symbol("y");
    const Expr rosen = parseExpr(c, "(1 - x)^2 + 100*(y - x^2)^2");

    const SymMatrix g = gradient(c, rosen, {x, y});
    ASSERT_EQ(g.rows(), 2u);
    ASSERT_EQ(g.cols(), 1u);
    EXPECT_TRUE(exprEq(c, g.at(0, 0), parseExpr(c, "400*x^3 - 400*x*y + 2*x - 2")));
    EXPECT_TRUE(exprEq(c, g.at(1, 0), parseExpr(c, "200*y - 200*x^2")));

    const SymMatrix H = hessian(c, rosen, {x, y});
    ASSERT_EQ(H.rows(), 2u);
    ASSERT_EQ(H.cols(), 2u);
    const SymMatrix wantH = parseMat(c, 2, 2, {
        "1200*x^2 - 400*y + 2", "-400*x",
        "-400*x",               "200"
    });
    EXPECT_TRUE(matEq(c, H, wantH));

    // At the global minimum (x, y) = (1, 1), grad = [0; 0] and det(H) = 400.
    const SymMatrix gAtMin = g.subs(c, x, c.one()).subs(c, y, c.one());
    EXPECT_TRUE(matEq(c, gAtMin, SymMatrix::zeros(c, 2, 1)));
    const SymMatrix HAtMin = H.subs(c, x, c.one()).subs(c, y, c.one());
    EXPECT_TRUE(exprEq(c, det(c, HAtMin), c.number(std::int64_t{400})));
}

TEST(SymMatrixTest, DeterminantVandermonde3x3)
{
    Ctx c;
    const SymMatrix V = parseMat(c, 3, 3, {
        "1", "x", "x^2",
        "1", "y", "y^2",
        "1", "z", "z^2"
    });
    const Expr d = det(c, V);
    const Expr want = parseExpr(c, "(y - x)*(z - x)*(z - y)");
    EXPECT_TRUE(exprEq(c, d, want))
        << "got: " << c.toString(d) << "\nwant: " << c.toString(want);
}

TEST(SymMatrixTest, CharpolyInverseAndLinsolveSymbolic)
{
    Ctx c;
    const Expr lam = c.symbol("lam");

    // 2x2 symbolic matrix [a, b; c, d]
    const SymMatrix A2 = parseMat(c, 2, 2, {"a", "b", "c", "d"});
    const Expr cp2 = charpoly(c, A2, lam);
    EXPECT_TRUE(exprEq(c, cp2, parseExpr(c, "lam^2 - (a + d)*lam + a*d - b*c")));

    const SymMatrix invA2 = inv(c, A2);
    ASSERT_FALSE(invA2.empty());
    EXPECT_TRUE(matEq(c, A2.mul(c, invA2), SymMatrix::eye(c, 2)));

    // Parametric 2x2 system: [x, 1; 1, x] * [u; v] = [x + 1; x + 1] => [1; 1]
    const SymMatrix M = parseMat(c, 2, 2, {"x", "1", "1", "x"});
    const SymMatrix rhs = parseMat(c, 2, 1, {"x + 1", "x + 1"});
    const SymMatrix sol = linsolve(c, M, rhs);
    ASSERT_EQ(sol.rows(), 2u);
    ASSERT_EQ(sol.cols(), 1u);
    EXPECT_TRUE(matEq(c, sol, parseMat(c, 2, 1, {"1", "1"})))
        << "got: " << sol.toString(c);

    // 3x3 symbolic system over Q(x)
    const SymMatrix A3 = parseMat(c, 3, 3, {
        "1", "x",     "0",
        "0", "1",     "x",
        "1", "0", "x^2 + 1"
    });
    const SymMatrix invA3 = inv(c, A3);
    ASSERT_FALSE(invA3.empty());
    EXPECT_TRUE(matEq(c, A3.mul(c, invA3), SymMatrix::eye(c, 3)))
        << "A3 * invA3 = " << A3.mul(c, invA3).toString(c);

    // Consistent overdetermined 3x2 system
    const SymMatrix Aover = parseMat(c, 3, 2, {
        "1", "2",
        "3", "4",
        "4", "6"
    });
    const SymMatrix Bover = parseMat(c, 3, 1, {"x + 2*y", "3*x + 4*y", "4*x + 6*y"});
    const SymMatrix Xover = linsolve(c, Aover, Bover);
    ASSERT_FALSE(Xover.empty());
    EXPECT_TRUE(matEq(c, Xover, parseMat(c, 2, 1, {"x", "y"})));

    // Inconsistent overdetermined 3x2 system returns empty matrix
    const SymMatrix Bincons = parseMat(c, 3, 1, {"1", "2", "4"});
    EXPECT_TRUE(linsolve(c, Aover, Bincons).empty());
}

// ============================================================================
// Layer 2: Property Tests
// ============================================================================

namespace {

SymMatrix randomPolyMatrix(Ctx &c, Expr x, std::size_t rows, std::size_t cols,
                           std::mt19937 &rng)
{
    std::uniform_int_distribution<int> cDist(-3, 3);
    SymMatrix M(rows, cols);
    for (std::size_t r = 0; r < rows; ++r) {
        for (std::size_t col = 0; col < cols; ++col) {
            const int c0 = cDist(rng);
            const int c1 = cDist(rng);
            M.at(r, col) = simplifyRationalExpr(
                c, c.add({c.number(static_cast<std::int64_t>(c0)),
                          c.mul({c.number(static_cast<std::int64_t>(c1)), x})}));
        }
    }
    return M;
}

} // namespace

TEST(SymMatrixTest, PropertyCayleyHamiltonAndAdjugate)
{
    Ctx c;
    const Expr x = c.symbol("x");
    const Expr lam = c.symbol("lam");
    std::mt19937 rng(0xCA11E401u);

    const SymMatrix I3 = SymMatrix::eye(c, 3);
    const SymMatrix Z3 = SymMatrix::zeros(c, 3, 3);

    for (int iter = 0; iter < 60; ++iter) {
        const SymMatrix A = randomPolyMatrix(c, x, 3, 3, rng);
        const Expr d = det(c, A);
        const SymMatrix adj = adjugate(c, A);
        ASSERT_FALSE(d.isNull());
        ASSERT_FALSE(adj.empty());

        // 1. A * adj(A) == det(A) * I_3 and adj(A) * A == det(A) * I_3
        const SymMatrix dI = I3.scale(c, d);
        EXPECT_TRUE(matEq(c, A.mul(c, adj), dI)) << "iter " << iter;
        EXPECT_TRUE(matEq(c, adj.mul(c, A), dI)) << "iter " << iter;

        // 2. Jacobi's formula: d/dx(det(A(x))) == trace(adj(A(x)) * dA/dx)
        const Expr dDet = simplifyRationalExpr(c, c.diff(d, x));
        const Expr trAdjDiff = adj.mul(c, A.diff(c, x)).trace(c);
        EXPECT_TRUE(exprEq(c, dDet, trAdjDiff)) << "iter " << iter;

        // 3. Cayley-Hamilton: p(A) = A^3 + c2*A^2 + c1*A + c0*I == 0
        // Extract coefficients of charpoly(A, lam) at lam = 0, d/dlam, etc.
        const Expr cp = charpoly(c, A, lam);
        const Expr c0 = c.subs(cp, lam, c.zero());
        const Expr dcp1 = c.diff(cp, lam);
        const Expr c1 = c.subs(dcp1, lam, c.zero());
        const Expr dcp2 = c.diff(dcp1, lam);
        const Expr c2 = simplifyRationalExpr(
            c, c.mul({c.number(Rational(std::int64_t{1}, BigInt(2))),
                      c.subs(dcp2, lam, c.zero())}));

        const SymMatrix A2 = A.mul(c, A);
        const SymMatrix A3 = A2.mul(c, A);
        const SymMatrix pA = A3.add(c, A2.scale(c, c2))
                                 .add(c, A.scale(c, c1))
                                 .add(c, I3.scale(c, c0));
        EXPECT_TRUE(matEq(c, pA, Z3)) << "iter " << iter;
    }
}

TEST(SymMatrixTest, PropertyLinsolveAndInverseRoundTrip)
{
    Ctx c;
    const Expr x = c.symbol("x");
    std::mt19937 rng(0x5017E302u);

    const SymMatrix I3 = SymMatrix::eye(c, 3);
    int tested = 0;
    for (int attempt = 0; attempt < 150 && tested < 50; ++attempt) {
        const SymMatrix A = randomPolyMatrix(c, x, 3, 3, rng);
        const Expr d = det(c, A);
        if (c.isZero(d))
            continue;
        ++tested;

        // 1. Inverse identity A * A^(-1) == I_3
        const SymMatrix invA = inv(c, A);
        ASSERT_FALSE(invA.empty());
        EXPECT_TRUE(matEq(c, A.mul(c, invA), I3));

        // 2. Linear solver round-trip: solve A * X = B where B = A * X_true
        const SymMatrix Xtrue = randomPolyMatrix(c, x, 3, 2, rng);
        const SymMatrix B = A.mul(c, Xtrue);
        const SymMatrix X = linsolve(c, A, B);
        ASSERT_FALSE(X.empty());
        EXPECT_TRUE(matEq(c, X, Xtrue));
        EXPECT_TRUE(matEq(c, A.mul(c, X), B));
    }
    EXPECT_EQ(tested, 50);
}

// ============================================================================
// Layer 3: Boundary Tests
// ============================================================================

TEST(SymMatrixTest, BoundaryAndSingularCases)
{
    Ctx c;

    // 1x1 matrix
    const SymMatrix A1 = parseMat(c, 1, 1, {"2*x + 3"});
    EXPECT_TRUE(exprEq(c, det(c, A1), parseExpr(c, "2*x + 3")));
    const SymMatrix invA1 = inv(c, A1);
    ASSERT_EQ(invA1.rows(), 1u);
    EXPECT_TRUE(exprEq(c, invA1.at(0, 0), parseExpr(c, "1/(2*x + 3)")));

    // Singular matrix: row 2 == x * row 1
    const SymMatrix Asing = parseMat(c, 2, 2, {"1", "x", "x", "x^2"});
    EXPECT_EQ(det(c, Asing), c.zero());
    EXPECT_TRUE(inv(c, Asing).empty());
    EXPECT_TRUE(linsolve(c, Asing, parseMat(c, 2, 1, {"1", "x"})).empty());

    // Dimension mismatches
    const SymMatrix R23 = SymMatrix::zeros(c, 2, 3);
    EXPECT_TRUE(R23.trace(c).isNull());
    EXPECT_TRUE(det(c, R23).isNull());
    EXPECT_TRUE(inv(c, R23).empty());
    EXPECT_TRUE(R23.add(c, A1).empty());
    EXPECT_TRUE(R23.mul(c, R23).empty());

    // Budget exhaustion
    Budget tiny(1);
    const SymMatrix A3 = SymMatrix::eye(c, 3);
    EXPECT_TRUE(det(c, A3, &tiny).isNull());
    EXPECT_EQ(tiny.status(), BudgetStatus::StepExhausted);
}

} // namespace
} // namespace numkit::cas
