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

TEST(SymMatrixTest, NullspaceEigenvaluesAndEigenvectors)
{
    Ctx c;

    // 1. Symmetric 2x2: [1, 2; 2, 1] -> eigenvalues -1, 3; eigenvectors [-1; 1], [1; 1]
    {
        const SymMatrix A = parseMat(c, 2, 2, {"1", "2", "2", "1"});
        const std::vector<Expr> evals = eigenvalues(c, A);
        ASSERT_EQ(evals.size(), 2u);
        EXPECT_EQ(evals[0], c.number(std::int64_t{-1}));
        EXPECT_EQ(evals[1], c.number(std::int64_t{3}));

        const std::vector<EigenPair> pairs = eigenvectors(c, A);
        ASSERT_EQ(pairs.size(), 2u);
        EXPECT_EQ(pairs[0].multiplicity, 1u);
        ASSERT_EQ(pairs[0].vectors.size(), 1u);
        EXPECT_TRUE(matEq(c, pairs[0].vectors[0],
                          parseMat(c, 2, 1, {"-1", "1"})));
        EXPECT_EQ(pairs[1].multiplicity, 1u);
        ASSERT_EQ(pairs[1].vectors.size(), 1u);
        EXPECT_TRUE(matEq(c, pairs[1].vectors[0],
                          parseMat(c, 2, 1, {"1", "1"})));
    }

    // 2. Defective 2x2 Jordan block: [2, 1; 0, 2] -> eigenvalue 2 (algebraic mult 2, geometric mult 1)
    {
        const SymMatrix J = parseMat(c, 2, 2, {"2", "1", "0", "2"});
        const std::vector<Expr> evals = eigenvalues(c, J);
        ASSERT_EQ(evals.size(), 2u);
        EXPECT_EQ(evals[0], c.number(std::int64_t{2}));
        EXPECT_EQ(evals[1], c.number(std::int64_t{2}));

        const std::vector<EigenPair> pairs = eigenvectors(c, J);
        ASSERT_EQ(pairs.size(), 1u);
        EXPECT_EQ(pairs[0].lambda, c.number(std::int64_t{2}));
        EXPECT_EQ(pairs[0].multiplicity, 2u);
        ASSERT_EQ(pairs[0].vectors.size(), 1u);
        EXPECT_TRUE(matEq(c, pairs[0].vectors[0],
                          parseMat(c, 2, 1, {"1", "0"})));
    }

    // 3. Diagonalizable 3x3 with repeated eigenvalue: diag-like with 2D eigenspace
    //    A = [2, 0, 0; 0, 2, 0; 0, 0, 5] -> lambda = 2 (mult 2, 2 vectors), lambda = 5 (mult 1, 1 vector)
    {
        const SymMatrix A = parseMat(
            c, 3, 3, {"2", "0", "0", "0", "2", "0", "0", "0", "5"});
        const std::vector<EigenPair> pairs = eigenvectors(c, A);
        ASSERT_EQ(pairs.size(), 2u);
        EXPECT_EQ(pairs[0].lambda, c.number(std::int64_t{2}));
        EXPECT_EQ(pairs[0].multiplicity, 2u);
        EXPECT_EQ(pairs[0].vectors.size(), 2u);
        EXPECT_EQ(pairs[1].lambda, c.number(std::int64_t{5}));
        EXPECT_EQ(pairs[1].multiplicity, 1u);
        EXPECT_EQ(pairs[1].vectors.size(), 1u);
    }

    // 4. Quadratic radical eigenvalues: [1, 1; 2, 1] -> lambda = 1 - sqrt(2), 1 + sqrt(2)
    {
        const SymMatrix A = parseMat(c, 2, 2, {"1", "1", "2", "1"});
        const SymMatrix I2 = SymMatrix::eye(c, 2);
        const std::vector<EigenPair> pairs = eigenvectors(c, A);
        ASSERT_EQ(pairs.size(), 2u);
        EXPECT_EQ(c.simplify(c.add({pairs[0].lambda,
                                    c.neg(parseExpr(c, "1 - 2^(1/2)"))})),
                  c.zero());
        EXPECT_EQ(c.simplify(c.add({pairs[1].lambda,
                                    c.neg(parseExpr(c, "1 + 2^(1/2)"))})),
                  c.zero());
        for (const auto &ep : pairs) {
            ASSERT_EQ(ep.vectors.size(), 1u);
            const SymMatrix res =
                A.sub(c, I2.scale(c, ep.lambda)).mul(c, ep.vectors[0]);
            EXPECT_EQ(c.simplify(res.at(0, 0)), c.zero());
            EXPECT_EQ(c.simplify(res.at(1, 0)), c.zero());
        }
    }

    // 5. Symbolic/parametric symmetric 2x2: [a, b; b, a] -> eigenvalues a - b, a + b
    {
        const SymMatrix A = parseMat(c, 2, 2, {"a", "b", "b", "a"});
        const SymMatrix I2 = SymMatrix::eye(c, 2);
        const std::vector<EigenPair> pairs = eigenvectors(c, A);
        ASSERT_EQ(pairs.size(), 2u);
        for (const auto &ep : pairs) {
            ASSERT_EQ(ep.vectors.size(), 1u);
            const SymMatrix res =
                A.sub(c, I2.scale(c, ep.lambda)).mul(c, ep.vectors[0]);
            EXPECT_EQ(c.simplify(res.at(0, 0)), c.zero());
            EXPECT_EQ(c.simplify(res.at(1, 0)), c.zero());
        }
    }

    // 6. Nullspace of rank-1 2x3 matrix: [1, 2, 3; 2, 4, 6] -> 2 basis vectors in R^3
    {
        const SymMatrix M =
            parseMat(c, 2, 3, {"1", "2", "3", "2", "4", "6"});
        const std::vector<SymMatrix> ns = nullspace(c, M);
        ASSERT_EQ(ns.size(), 2u);
        const SymMatrix Z21 = SymMatrix::zeros(c, 2, 1);
        for (const auto &v : ns) {
            EXPECT_TRUE(matEq(c, M.mul(c, v), Z21));
        }
    }
}

TEST(SymMatrixTest, MatrixExponentialIdentities)
{
    Ctx c;
    const Expr t = c.symbol("t");

    // 1. Rotation generator: [0, -w; w, 0] -> [cos(w*t), -sin(w*t); sin(w*t), cos(w*t)]
    {
        const SymMatrix A = parseMat(c, 2, 2, {"0", "-3", "3", "0"});
        const SymMatrix Phi = matrixExp(c, A, t);
        ASSERT_FALSE(Phi.empty());
        EXPECT_EQ(c.simplify(c.add({Phi.at(0, 0), c.neg(parseExpr(c, "cos(3*t)"))})),
                  c.zero());
        EXPECT_EQ(c.simplify(c.add({Phi.at(0, 1), c.neg(parseExpr(c, "-sin(3*t)"))})),
                  c.zero());
        EXPECT_EQ(c.simplify(c.add({Phi.at(1, 0), c.neg(parseExpr(c, "sin(3*t)"))})),
                  c.zero());
        EXPECT_EQ(c.simplify(c.add({Phi.at(1, 1), c.neg(parseExpr(c, "cos(3*t)"))})),
                  c.zero());
    }

    // 2. 3x3 nilpotent/Jordan block: [2, 1, 0; 0, 2, 1; 0, 0, 2]
    //    -> exp(2*t) * [1, t, 1/2*t^2; 0, 1, t; 0, 0, 1]
    {
        const SymMatrix J3 = parseMat(
            c, 3, 3, {"2", "1", "0", "0", "2", "1", "0", "0", "2"});
        const SymMatrix Phi = matrixExp(c, J3, t);
        ASSERT_FALSE(Phi.empty());
        EXPECT_EQ(c.simplify(c.add({Phi.at(0, 2),
                                    c.neg(parseExpr(c, "1/2*t^2*exp(2*t)"))})),
                  c.zero());
    }
}

TEST(SymMatrixTest, RrefRankAndLUDecomposition)
{
    Ctx c;

    // 1. RREF and rank on rank-2 3x4 matrix
    {
        const SymMatrix A = parseMat(
            c, 3, 4,
            {"1", "2", "1", "1",
             "2", "4", "2", "2",
             "1", "2", "3", "4"});
        std::vector<std::size_t> pivs;
        const SymMatrix R = rref(c, A, &pivs);
        ASSERT_FALSE(R.empty());
        EXPECT_EQ(rank(c, A), 2u);
        ASSERT_EQ(pivs.size(), 2u);
        EXPECT_EQ(pivs[0], 0u);
        EXPECT_EQ(pivs[1], 2u);
        const SymMatrix wantR = parseMat(
            c, 3, 4,
            {"1", "2", "0", "-1/2",
             "0", "0", "1", "3/2",
             "0", "0", "0", "0"});
        EXPECT_TRUE(matEq(c, R, wantR));
    }

    // 2. Pivoted LU decomposition on matrix with zero leading entry:
    //    [0, 2, 1; 1, 1, 2; 2, 3, 1]
    {
        const SymMatrix A = parseMat(
            c, 3, 3,
            {"0", "2", "1",
             "1", "1", "2",
             "2", "3", "1"});
        const LUDecomposition d = lu(c, A);
        ASSERT_TRUE(d.proved()) << d.reason;
        EXPECT_TRUE(matEq(c, d.P.mul(c, A), d.L.mul(c, d.U)));
        // det(A) = sign * U(0,0) * U(1,1) * U(2,2)
        const Expr detFromLU = c.mul(
            {c.number(d.sign), d.U.at(0, 0), d.U.at(1, 1), d.U.at(2, 2)});
        EXPECT_EQ(c.simplify(c.add({detFromLU, c.neg(det(c, A))})), c.zero());
    }

    // 3. Symbolic LU decomposition: [a, b; c, d]
    {
        const SymMatrix A = parseMat(c, 2, 2, {"a", "b", "c", "d"});
        const LUDecomposition d = lu(c, A);
        ASSERT_TRUE(d.proved()) << d.reason;
        EXPECT_TRUE(matEq(c, d.P.mul(c, A), d.L.mul(c, d.U)));
    }

    // 4. Property: 50 random 3x4 and 4x3 integer matrices satisfy P * A == L * U
    std::mt19937_64 rng(0x4C5550524F50ULL);
    std::uniform_int_distribution<int> entryDist(-4, 4);
    for (int iter = 0; iter < 50; ++iter) {
        const std::size_t rows = (iter % 2 == 0) ? 3 : 4;
        const std::size_t cols = (iter % 2 == 0) ? 4 : 3;
        SymMatrix M(rows, cols);
        for (std::size_t r = 0; r < rows; ++r)
            for (std::size_t j = 0; j < cols; ++j)
                M.at(r, j) = c.number(entryDist(rng));
        const LUDecomposition d = lu(c, M);
        ASSERT_TRUE(d.proved()) << "iter " << iter << ": " << d.reason;
        EXPECT_TRUE(matEq(c, d.P.mul(c, M), d.L.mul(c, d.U)));
    }
}

TEST(SymMatrixTest, GramSchmidtAndQRDecomposition)
{
    Ctx c;

    // 1. Classical 3x3 matrix with integer column norms (3-4-5 / 1-2-2):
    //    A = [12, -51, 4; 6, 167, -68; -4, 24, -41]
    {
        const SymMatrix A = parseMat(
            c, 3, 3,
            {"12", "-51", "4",
             "6", "167", "-68",
             "-4", "24", "-41"});
        const QRDecomposition d = qr(c, A);
        ASSERT_TRUE(d.proved()) << d.reason;
        EXPECT_TRUE(matEq(c, d.Q.mul(c, d.R), A));
        EXPECT_TRUE(matEq(c, d.Q.transpose().mul(c, d.Q), SymMatrix::eye(c, 3)));
        EXPECT_EQ(d.R.at(0, 0), c.number(14));
        EXPECT_EQ(d.R.at(1, 1), c.number(175));
        EXPECT_EQ(d.R.at(2, 2), c.number(35));
    }

    // 2. Rectangular 3x2 matrix with radical norms: A = [1, 1; 1, 0; 0, 1]
    {
        const SymMatrix A = parseMat(
            c, 3, 2,
            {"1", "1",
             "1", "0",
             "0", "1"});
        const QRDecomposition d = qr(c, A);
        ASSERT_TRUE(d.proved()) << d.reason;
        for (std::size_t r = 0; r < 3; ++r) {
            for (std::size_t j = 0; j < 2; ++j) {
                const Expr diffEntry =
                    c.add({d.Q.mul(c, d.R).at(r, j), c.neg(A.at(r, j))});
                EXPECT_EQ(c.simplify(diffEntry), c.zero());
            }
        }
        const SymMatrix QtQ = d.Q.transpose().mul(c, d.Q);
        for (std::size_t i = 0; i < 2; ++i) {
            for (std::size_t j = 0; j < 2; ++j) {
                const Expr want = (i == j) ? c.one() : c.zero();
                EXPECT_EQ(c.simplify(c.add({QtQ.at(i, j), c.neg(want)})),
                          c.zero());
            }
        }
    }

    // 3. gramSchmidt drops linearly dependent columns
    {
        const SymMatrix v1 = SymMatrix::column({c.one(), c.one(), c.zero()});
        const SymMatrix v2 = SymMatrix::column({c.number(2), c.number(2), c.zero()});
        const SymMatrix v3 = SymMatrix::column({c.one(), c.zero(), c.one()});
        const std::vector<SymMatrix> ortho =
            gramSchmidt(c, {v1, v2, v3}, false);
        ASSERT_EQ(ortho.size(), 2u);
        const SymMatrix ip = ortho[0].transpose().mul(c, ortho[1]);
        EXPECT_EQ(c.simplify(ip.at(0, 0)), c.zero());
    }
}

TEST(SymMatrixTest, JordanCanonicalForm)
{
    Ctx c;

    // 1. Diagonalizable 2x2 matrix: [4, 1; 2, 3] -> eigenvalues 2, 5
    {
        const SymMatrix A = parseMat(c, 2, 2, {"4", "1", "2", "3"});
        const JordanDecomposition jd = jordanForm(c, A);
        ASSERT_TRUE(jd.proved()) << jd.reason;
        EXPECT_TRUE(matEq(c, A.mul(c, jd.P), jd.P.mul(c, jd.J)));
        EXPECT_TRUE(matEq(c, jd.P.mul(c, jd.PInv), SymMatrix::eye(c, 2)));
        EXPECT_EQ(jd.J.at(0, 0), c.number(2));
        EXPECT_EQ(jd.J.at(1, 1), c.number(5));
        EXPECT_EQ(jd.J.at(0, 1), c.zero());
    }

    // 2. Defective 2x2 matrix: [3, 1; -1, 1] -> double eigenvalue 2, single 2x2 Jordan block
    {
        const SymMatrix A = parseMat(c, 2, 2, {"3", "1", "-1", "1"});
        const JordanDecomposition jd = jordanForm(c, A);
        ASSERT_TRUE(jd.proved()) << jd.reason;
        EXPECT_TRUE(matEq(c, A.mul(c, jd.P), jd.P.mul(c, jd.J)));
        EXPECT_TRUE(matEq(c, jd.P.mul(c, jd.PInv), SymMatrix::eye(c, 2)));
        EXPECT_EQ(jd.J.at(0, 0), c.number(2));
        EXPECT_EQ(jd.J.at(0, 1), c.one());
        EXPECT_EQ(jd.J.at(1, 0), c.zero());
        EXPECT_EQ(jd.J.at(1, 1), c.number(2));
    }

    // 3. Defective 3x3 matrix with a single 3x3 Jordan block at lambda = 2:
    //    P * [2, 1, 0; 0, 2, 1; 0, 0, 2] * P^(-1)
    {
        const SymMatrix P0 = parseMat(
            c, 3, 3,
            {"1", "1", "0",
             "0", "1", "1",
             "1", "0", "1"});
        const SymMatrix J0 = parseMat(
            c, 3, 3,
            {"2", "1", "0",
             "0", "2", "1",
             "0", "0", "2"});
        const SymMatrix A = P0.mul(c, J0).mul(c, inv(c, P0));
        const JordanDecomposition jd = jordanForm(c, A);
        ASSERT_TRUE(jd.proved()) << jd.reason;
        EXPECT_TRUE(matEq(c, jd.J, J0));
        EXPECT_TRUE(matEq(c, A.mul(c, jd.P), jd.P.mul(c, jd.J)));
    }

    // 4. Defective 3x3 matrix with mixed (2 + 1) Jordan blocks at the SAME eigenvalue lambda = 3:
    //    J0 = [3, 1, 0; 0, 3, 0; 0, 0, 3]
    {
        const SymMatrix P0 = parseMat(
            c, 3, 3,
            {"1", "2", "1",
             "0", "1", "1",
             "1", "1", "2"});
        const SymMatrix J0 = parseMat(
            c, 3, 3,
            {"3", "1", "0",
             "0", "3", "0",
             "0", "0", "3"});
        const SymMatrix A = P0.mul(c, J0).mul(c, inv(c, P0));
        const JordanDecomposition jd = jordanForm(c, A);
        ASSERT_TRUE(jd.proved()) << jd.reason;
        EXPECT_TRUE(matEq(c, jd.J, J0));
        EXPECT_TRUE(matEq(c, A.mul(c, jd.P), jd.P.mul(c, jd.J)));
    }

    // 5. Defective 4x4 matrix with two 2x2 Jordan blocks at the SAME eigenvalue lambda = -1:
    //    J0 = [-1, 1, 0, 0; 0, -1, 0, 0; 0, 0, -1, 1; 0, 0, 0, -1]
    {
        const SymMatrix P0 = parseMat(
            c, 4, 4,
            {"1", "1", "0", "0",
             "0", "1", "1", "0",
             "0", "0", "1", "1",
             "1", "0", "0", "2"});
        const SymMatrix J0 = parseMat(
            c, 4, 4,
            {"-1", "1", "0", "0",
             "0", "-1", "0", "0",
             "0", "0", "-1", "1",
             "0", "0", "0", "-1"});
        const SymMatrix A = P0.mul(c, J0).mul(c, inv(c, P0));
        const JordanDecomposition jd = jordanForm(c, A);
        ASSERT_TRUE(jd.proved()) << jd.reason;
        EXPECT_TRUE(matEq(c, jd.J, J0));
        EXPECT_TRUE(matEq(c, A.mul(c, jd.P), jd.P.mul(c, jd.J)));
    }
}

TEST(SymMatrixTest, VectorCalculusDivergenceCurlLaplacianWronskianAndPotential)
{
    Ctx c;
    const Expr x = c.symbol("x");
    const Expr y = c.symbol("y");
    const Expr z = c.symbol("z");
    const std::vector<Expr> vars3 = {x, y, z};

    // 1. Divergence, curl, and Laplacian fixed vectors
    {
        const std::vector<Expr> F = {
            parseExpr(c, "x^2*y"),
            parseExpr(c, "y^2*z"),
            parseExpr(c, "z^2*x")};
        const Expr divF = divergence(c, F, vars3);
        EXPECT_EQ(c.toString(divF), "2*x*y + 2*x*z + 2*y*z");

        const SymMatrix curlF = curl(c, F, vars3);
        ASSERT_EQ(curlF.rows(), 3u);
        ASSERT_EQ(curlF.cols(), 1u);
        EXPECT_EQ(c.toString(curlF.at(0, 0)), "-y^2");
        EXPECT_EQ(c.toString(curlF.at(1, 0)), "-z^2");
        EXPECT_EQ(c.toString(curlF.at(2, 0)), "-x^2");

        // Identity: div(curl(F)) == 0
        const std::vector<Expr> curlVec = {
            curlF.at(0, 0), curlF.at(1, 0), curlF.at(2, 0)};
        EXPECT_TRUE(c.isZero(divergence(c, curlVec, vars3)));

        // Harmonic 3D potential r^(-1) -> Laplacian == 0 ( tested on polynomial x^3 - 3*x*y^2 )
        const Expr harm = parseExpr(c, "x^3 - 3*x*y^2 + 2*z^2 - 2*x^2");
        EXPECT_EQ(c.toString(laplacian(c, harm, vars3)), "0");

        // Identity: curl(grad(phi)) == 0 and div(grad(phi)) == laplacian(phi)
        const Expr phi = parseExpr(c, "x^2*y*z + sin(x)*cos(y) + exp(z)");
        const SymMatrix gradPhi = gradient(c, phi, vars3);
        const std::vector<Expr> gradVec = {
            gradPhi.at(0, 0), gradPhi.at(1, 0), gradPhi.at(2, 0)};
        const SymMatrix curlGrad = curl(c, gradVec, vars3);
        EXPECT_TRUE(c.isZero(curlGrad.at(0, 0)));
        EXPECT_TRUE(c.isZero(curlGrad.at(1, 0)));
        EXPECT_TRUE(c.isZero(curlGrad.at(2, 0)));
        EXPECT_TRUE(c.isZero(c.simplify(c.add(
            {divergence(c, gradVec, vars3), c.neg(laplacian(c, phi, vars3))}))));
    }

    // 2. Wronskian matrix and determinant
    {
        // W(cos(x), sin(x)) = 1
        const Expr wTrig = wronskian(
            c, {parseExpr(c, "cos(x)"), parseExpr(c, "sin(x)")}, x);
        EXPECT_EQ(c.toString(wTrig), "1");

        // W(1, x, x^2) = 2
        const Expr wPoly = wronskian(
            c, {c.one(), x, parseExpr(c, "x^2")}, x);
        EXPECT_EQ(c.toString(wPoly), "2");

        // W(exp(x), x*exp(x), x^2*exp(x)) = 2*exp(3*x)
        const Expr wExp = wronskian(
            c,
            {parseExpr(c, "exp(x)"),
             parseExpr(c, "x*exp(x)"),
             parseExpr(c, "x^2*exp(x)")},
            x);
        EXPECT_EQ(c.toString(wExp), "2*exp(3*x)");
    }

    // 3. Certified scalar potential reconstruction (`scalarPotential`)
    {
        // Conservative 3D field: grad(x^2*y + y*z^3 + cos(x))
        const Expr phiTrue = parseExpr(c, "x^2*y + y*z^3 + cos(x)");
        const SymMatrix g = gradient(c, phiTrue, vars3);
        const std::vector<Expr> F = {g.at(0, 0), g.at(1, 0), g.at(2, 0)};
        const PotentialResult pot = scalarPotential(c, F, vars3);
        ASSERT_TRUE(pot.proved()) << pot.reason;
        // Difference between pot.phi and phiTrue must be constant in (x, y, z)
        const SymMatrix gDiff =
            gradient(c, c.add({pot.phi, c.neg(phiTrue)}), vars3);
        EXPECT_TRUE(c.isZero(c.simplify(gDiff.at(0, 0))));
        EXPECT_TRUE(c.isZero(c.simplify(gDiff.at(1, 0))));
        EXPECT_TRUE(c.isZero(c.simplify(gDiff.at(2, 0))));

        // Non-conservative field F = (-y, x, 0) -> Unevaluated
        const PotentialResult nonCons =
            scalarPotential(c, {c.neg(y), x, c.zero()}, vars3);
        EXPECT_FALSE(nonCons.proved());
    }
}

TEST(SymMatrixTest, LagrangeExtremaUnconstrainedAndConstrained)
{
    Ctx c;
    const Expr x = c.symbol("x");
    const Expr y = c.symbol("y");
    const Expr z = c.symbol("z");

    // 1. Unconstrained critical points with Hessian classification:
    //    f(x, y) = x^3 - 3*x + y^2 - 4*y
    //    df/dx = 3*(x^2 - 1) = 0 => x = +-1
    //    df/dy = 2*(y - 2) = 0   => y = 2
    //    H = diag(6*x, 2):
    //      (-1, 2): H = diag(-6, 2) -> SaddlePoint, f = -2
    //      ( 1, 2): H = diag( 6, 2) -> LocalMinimum, f = -6
    {
        const Expr f = parseExpr(c, "x^3 - 3*x + y^2 - 4*y");
        const LagrangeExtremaResult res = lagrangeExtrema(c, f, {x, y});
        ASSERT_TRUE(res.proved()) << res.reason;
        EXPECT_TRUE(res.certified);
        ASSERT_EQ(res.points.size(), 2u);

        EXPECT_EQ(res.points[0].point[0], c.number(-1));
        EXPECT_EQ(res.points[0].point[1], c.number(2));
        EXPECT_EQ(res.points[0].value, c.number(-2));
        EXPECT_EQ(res.points[0].kind,
                  ExtremumPoint::Classification::SaddlePoint);

        EXPECT_EQ(res.points[1].point[0], c.number(1));
        EXPECT_EQ(res.points[1].point[1], c.number(2));
        EXPECT_EQ(res.points[1].value, c.number(-6));
        EXPECT_EQ(res.points[1].kind,
                  ExtremumPoint::Classification::LocalMinimum);
    }

    // 2. Constrained extremum on a line:
    //    minimize f(x, y) = x^2 + y^2 subject to x + y - 2 = 0
    //    -> unique minimum at (1, 1) with lambda = 2, f(1, 1) = 2
    {
        const Expr f = parseExpr(c, "x^2 + y^2");
        const Expr g = parseExpr(c, "x + y - 2");
        const LagrangeExtremaResult res = lagrangeExtrema(c, f, {x, y}, {g});
        ASSERT_TRUE(res.proved()) << res.reason;
        EXPECT_TRUE(res.certified);
        ASSERT_EQ(res.points.size(), 1u);
        EXPECT_EQ(res.points[0].point[0], c.one());
        EXPECT_EQ(res.points[0].point[1], c.one());
        EXPECT_EQ(res.points[0].multipliers[0], c.number(2));
        EXPECT_EQ(res.points[0].value, c.number(2));
        EXPECT_EQ(res.points[0].kind,
                  ExtremumPoint::Classification::LocalMinimum);
    }

    // 3. Constrained extrema on unit circle:
    //    f(x, y) = x + y subject to x^2 + y^2 - 1 = 0
    //    -> (-2^(-1/2), -2^(-1/2)) [LocalMinimum, f = -2^(1/2)]
    //    -> ( 2^(-1/2),  2^(-1/2)) [LocalMaximum, f =  2^(1/2)]
    {
        const Expr f = parseExpr(c, "x + y");
        const Expr g = parseExpr(c, "x^2 + y^2 - 1");
        const LagrangeExtremaResult res = lagrangeExtrema(c, f, {x, y}, {g});
        ASSERT_TRUE(res.proved()) << res.reason;
        EXPECT_TRUE(res.certified);
        ASSERT_EQ(res.points.size(), 2u);
        const Expr sqrt2 = parseExpr(c, "2^(1/2)");
        EXPECT_EQ(c.simplify(c.add({res.points[0].value, sqrt2})), c.zero());
        EXPECT_EQ(res.points[0].kind,
                  ExtremumPoint::Classification::LocalMinimum);
        EXPECT_EQ(c.simplify(c.add({res.points[1].value, c.neg(sqrt2)})),
                  c.zero());
        EXPECT_EQ(res.points[1].kind,
                  ExtremumPoint::Classification::LocalMaximum);
    }

    // 4. 3D constrained optimization with 2 equality constraints:
    //    minimize f(x, y, z) = x^2 + y^2 + z^2 subject to
    //      x + y + z - 3 = 0 and x - y = 0
    //    -> unique stationary point (1, 1, 1) with f = 3, multipliers (2, 0)
    {
        const Expr f = parseExpr(c, "x^2 + y^2 + z^2");
        const Expr g1 = parseExpr(c, "x + y + z - 3");
        const Expr g2 = parseExpr(c, "x - y");
        const LagrangeExtremaResult res =
            lagrangeExtrema(c, f, {x, y, z}, {g1, g2});
        ASSERT_TRUE(res.proved()) << res.reason;
        EXPECT_TRUE(res.certified);
        ASSERT_EQ(res.points.size(), 1u);
        EXPECT_EQ(res.points[0].point[0], c.one());
        EXPECT_EQ(res.points[0].point[1], c.one());
        EXPECT_EQ(res.points[0].point[2], c.one());
        EXPECT_EQ(res.points[0].value, c.number(3));
        EXPECT_EQ(res.points[0].multipliers[0], c.number(2));
        EXPECT_EQ(res.points[0].multipliers[1], c.zero());
    }
}

TEST(SymMatrixTest, EulerLagrangePoissonBracketAndHamiltonEquations)
{
    Ctx c;
    const Expr t = c.symbol("t");
    const Expr q = c.symbol("q");
    const Expr dq = c.symbol("dq");
    const Expr ddq = c.symbol("ddq");
    const Expr d3q = c.symbol("d3q");
    const Expr d4q = c.symbol("d4q");
    const Expr r = c.symbol("r");
    const Expr dr = c.symbol("dr");
    const Expr ddr = c.symbol("ddr");
    const Expr phi = c.symbol("phi");
    const Expr dphi = c.symbol("dphi");
    const Expr ddphi = c.symbol("ddphi");

    // 1. 1D harmonic oscillator L = 1/2*m*dq^2 - 1/2*k*q^2:
    //    E(L) = -k*q - m*ddq == 0, E_beltrami = 1/2*m*dq^2 + 1/2*k*q^2
    {
        const Expr L = parseExpr(c, "1/2*m*dq^2 - 1/2*k*q^2");
        const EulerLagrangeResult el = eulerLagrange(c, L, t, q, dq, ddq);
        ASSERT_EQ(el.equations.size(), 1u);
        EXPECT_TRUE(el.autonomous);
        EXPECT_EQ(c.simplify(c.add({el.equations[0],
                                    parseExpr(c, "m*ddq + k*q")})),
                  c.zero());
        EXPECT_EQ(c.simplify(c.add({el.energy,
                                    c.neg(parseExpr(c, "1/2*m*dq^2 + 1/2*k*q^2"))})),
                  c.zero());
    }

    // 2. Central-force Kepler problem in polar coordinates (r, phi):
    //    L = 1/2*m*(dr^2 + r^2*dphi^2) + k/r
    //    - phi is cyclic (dL/dphi == 0) with conserved angular momentum p_phi = m*r^2*dphi
    //    - E_r(L) = m*r*dphi^2 - k/r^2 - m*ddr
    //    - E_phi(L) = -(m*r^2*ddphi + 2*m*r*dr*dphi)
    {
        const Expr L =
            parseExpr(c, "1/2*m*(dr^2 + r^2*dphi^2) + k*r^(-1)");
        const EulerLagrangeResult el =
            eulerLagrange(c, L, t, {r, phi}, {dr, dphi}, {ddr, ddphi});
        ASSERT_EQ(el.equations.size(), 2u);
        ASSERT_EQ(el.cyclicCoords.size(), 1u);
        EXPECT_EQ(el.cyclicCoords[0], phi);
        EXPECT_EQ(el.conservedMomenta[0],
                  c.simplify(parseExpr(c, "m*r^2*dphi")));
        EXPECT_EQ(c.simplify(c.add({
                      el.equations[0],
                      c.neg(parseExpr(c, "m*r*dphi^2 - k*r^(-2) - m*ddr"))})),
                  c.zero());
        EXPECT_EQ(c.simplify(c.add({
                      el.equations[1],
                      parseExpr(c, "m*r^2*ddphi + 2*m*r*dr*dphi")})),
                  c.zero());
    }

    // 3. Higher-order Euler-Poisson equation (Euler-Bernoulli beam functional):
    //    L = 1/2*EI*ddq^2 - f0*q -> E(L) = -f0 + EI*d4q == 0
    {
        const Expr L = parseExpr(c, "1/2*EI*ddq^2 - f0*q");
        const EulerLagrangeResult el = eulerLagrange(
            c, L, t, {VariationalField{q, {dq, ddq, d3q, d4q}}});
        ASSERT_EQ(el.equations.size(), 1u);
        EXPECT_EQ(c.simplify(c.add({el.equations[0],
                                    c.neg(parseExpr(c, "EI*d4q - f0"))})),
                  c.zero());
    }

    // 4. Canonical Poisson brackets: angular momentum SO(3) Lie algebra
    //    {L_x, L_y} = L_z, {L_y, L_z} = L_x, {L_z, L_x} = L_y, and Jacobi identity
    {
        const Expr x = c.symbol("x");
        const Expr y = c.symbol("y");
        const Expr z = c.symbol("z");
        const Expr px = c.symbol("px");
        const Expr py = c.symbol("py");
        const Expr pz = c.symbol("pz");
        const std::vector<Expr> qVec{x, y, z};
        const std::vector<Expr> pVec{px, py, pz};
        const Expr Lx = parseExpr(c, "y*pz - z*py");
        const Expr Ly = parseExpr(c, "z*px - x*pz");
        const Expr Lz = parseExpr(c, "x*py - y*px");

        EXPECT_EQ(poissonBracket(c, Lx, Ly, qVec, pVec), c.simplify(Lz));
        EXPECT_EQ(poissonBracket(c, Ly, Lz, qVec, pVec), c.simplify(Lx));
        EXPECT_EQ(poissonBracket(c, Lz, Lx, qVec, pVec), c.simplify(Ly));

        // Jacobi identity: {{Lx, Ly}, r^2} + {{Ly, r^2}, Lx} + {{r^2, Lx}, Ly} == 0
        const Expr r2 = parseExpr(c, "x^2 + y^2 + z^2");
        const Expr jacobi = c.simplify(c.add({
            poissonBracket(c, poissonBracket(c, Lx, Ly, qVec, pVec), r2, qVec, pVec),
            poissonBracket(c, poissonBracket(c, Ly, r2, qVec, pVec), Lx, qVec, pVec),
            poissonBracket(c, poissonBracket(c, r2, Lx, qVec, pVec), Ly, qVec, pVec)}));
        EXPECT_EQ(jacobi, c.zero());
    }

    // 5. Legendre transformation & canonical Hamilton equations:
    //    Charged particle in uniform magnetic field (symmetric gauge):
    //    L = 1/2*m*(dx^2 + dy^2) + 1/2*B*(x*dy - y*dx) - 1/2*k*(x^2 + y^2)
    {
        const Expr x = c.symbol("x");
        const Expr y = c.symbol("y");
        const Expr dx = c.symbol("dx");
        const Expr dy = c.symbol("dy");
        const Expr px = c.symbol("px");
        const Expr py = c.symbol("py");
        const Expr L = parseExpr(
            c, "1/2*m*(dx^2 + dy^2) + 1/2*B*(x*dy - y*dx) - 1/2*k*(x^2 + y^2)");
        const HamiltonEquationsResult ham =
            legendreTransform(c, L, {x, y}, {dx, dy}, {px, py});
        ASSERT_TRUE(ham.certified) << ham.reason;
        const Expr expectedH = parseExpr(
            c, "1/2*m^(-1)*((px + 1/2*B*y)^2 + (py - 1/2*B*x)^2) + 1/2*k*(x^2 + y^2)");
        EXPECT_EQ(c.simplify(c.expand(c.add({ham.H, c.neg(expectedH)}))),
                  c.zero());
        EXPECT_EQ(c.simplify(c.add({
                      ham.dqdt[0],
                      c.neg(parseExpr(c, "m^(-1)*(px + 1/2*B*y)"))})),
                  c.zero());
        EXPECT_EQ(c.simplify(c.add({
                      ham.dqdt[1],
                      c.neg(parseExpr(c, "m^(-1)*(py - 1/2*B*x)"))})),
                  c.zero());
    }
}

} // namespace
} // namespace numkit::cas
