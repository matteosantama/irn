"""Larger sparse QP: tridiagonal P with sparse random A.

Solves
    min  1/2 x^T P x + c^T x
    s.t. A x <= b, x >= 0,
with n = 50 variables, m = 80 inequality constraints (plus 50 bound
constraints), P tridiagonal SPD, A sparse (~10 nonzeros per row).
Cross-checks against scipy.optimize.minimize.

Total system size: 131 x 131. The H_k + M matrix the solver factorises
each Newton step inherits the sparsity of P and A.
"""

import numpy as np
import scipy.sparse as sp
from scipy.optimize import minimize

from irn import solve


def build_problem(n: int, m: int, seed: int = 0):
    rng = np.random.default_rng(seed)

    # Tridiagonal P: P_{i,i} = 2, P_{i,i-1} = P_{i-1,i} = -0.5  (SPD).
    main_diag = 2.0 * np.ones(n)
    off_diag = -0.5 * np.ones(n - 1)
    P = sp.diags_array(
        [off_diag, main_diag, off_diag], offsets=[-1, 0, 1], format="csc"
    )

    # Sparse A: ~10 nonzeros per row, signs/magnitudes drawn from N(0, 1).
    nnz_per_row = 10
    rows = np.repeat(np.arange(m), nnz_per_row)
    cols = np.concatenate([rng.choice(n, size=nnz_per_row, replace=False) for _ in range(m)])
    vals = rng.standard_normal(m * nnz_per_row)
    A_random = sp.csc_array((vals, (rows, cols)), shape=(m, n))

    # Append x >= 0 (as -I x <= 0) so the cone constraint x >= 0 is
    # explicit in the formulation.
    A_bounds = -sp.eye_array(n, format="csc")
    A = sp.vstack([A_random, A_bounds], format="csc")

    b_random = np.abs(rng.standard_normal(m)) + 0.5
    b = np.concatenate([b_random, np.zeros(n)])

    c = rng.standard_normal(n)

    return P, A, b, c


def reference(P_dense, A_dense, b, c):
    constraints = [{"type": "ineq", "fun": lambda x, A=A_dense, b=b: b - A @ x}]
    res = minimize(
        fun=lambda x: 0.5 * x @ P_dense @ x + c @ x,
        jac=lambda x: P_dense @ x + c,
        x0=np.zeros(len(c)),
        method="SLSQP",
        constraints=constraints,
        options={"ftol": 1e-12, "maxiter": 1000},
    )
    return res.x, float(res.fun)


def main() -> None:
    n, m = 50, 80
    P, A, b, c = build_problem(n=n, m=m, seed=7)

    print(f"problem    : n={n}, m={m + n}")
    print(f"P nnz      : {P.nnz}/{n * n}  ({100 * P.nnz / (n * n):.1f}%)")
    print(f"A nnz      : {A.nnz}/{A.shape[0] * A.shape[1]}  "
          f"({100 * A.nnz / (A.shape[0] * A.shape[1]):.1f}%)")
    print()

    result = solve(P, A, b, c)

    print(f"status     : {result.status}")
    print(f"iterations : {result.iterations}")
    print(f"objective  : {result.objective:+.6f}")
    print(f"final mu   : {result.mu:.2e}")
    print(f"||x||_inf  : {float(np.max(np.abs(result.x))):.4f}")
    print(f"min(s)     : {float(np.min(result.s)):.2e}    (should be >= ~0)")

    x_ref, obj_ref = reference(P.toarray(), A.toarray(), b, c)
    print()
    print(f"scipy obj  : {obj_ref:+.6f}")
    print(f"|obj - obj_ref|     = {abs(result.objective - obj_ref):.2e}")
    print(f"||x - x_ref||_inf   = {float(np.max(np.abs(result.x - x_ref))):.2e}")

    np.testing.assert_allclose(result.objective, obj_ref, atol=1e-5)
    assert result.status == "optimal", result.status
    print("\nOK")


if __name__ == "__main__":
    main()
