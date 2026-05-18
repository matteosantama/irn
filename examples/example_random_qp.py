"""Random convex QP stress test with sparse inputs.

Generates a small dense QP, converts P and A to scipy sparse CSC, and
cross-checks the IRN solution against scipy.optimize.minimize.
"""

import numpy as np
import scipy.sparse as sp
from scipy.optimize import minimize

from irn import solve


def random_qp(n_vars: int, n_ineq: int, seed: int = 0):
    rng = np.random.default_rng(seed)
    L = rng.standard_normal((n_vars, n_vars))
    P = L @ L.T / n_vars + 0.1 * np.eye(n_vars)
    c = rng.standard_normal(n_vars)
    A_ineq = rng.standard_normal((n_ineq, n_vars))
    b_ineq = np.abs(rng.standard_normal(n_ineq)) + 0.5
    A_full = np.vstack([A_ineq, -np.eye(n_vars)])
    b_full = np.concatenate([b_ineq, np.zeros(n_vars)])
    return P, A_full, b_full, c


def reference_qp(P, A, b, c, x0):
    constraints = [{"type": "ineq", "fun": lambda x, A=A, b=b: b - A @ x}]
    res = minimize(
        fun=lambda x: 0.5 * x @ P @ x + c @ x,
        jac=lambda x: P @ x + c,
        x0=x0,
        method="SLSQP",
        constraints=constraints,
        options={"ftol": 1e-12, "maxiter": 500},
    )
    return res.x, float(res.fun)


def main() -> None:
    P_dense, A_dense, b, c = random_qp(n_vars=6, n_ineq=8, seed=42)

    # Pass P and A as sparse CSC arrays.
    P = sp.csc_array(P_dense)
    A = sp.csc_array(A_dense)

    result = solve(P, A, b, c, verbose=False)
    x_ref, obj_ref = reference_qp(P_dense, A_dense, b, c, x0=np.zeros(len(c)))

    print(f"status     : {result.status}")
    print(f"iterations : {result.iterations}")
    print(f"objective  : {result.objective:+.6f}    (scipy: {obj_ref:+.6f})")
    print(f"final mu   : {result.mu:.2e}")
    print()
    print(f"x (IRN)    : {result.x}")
    print(f"x (scipy)  : {x_ref}")
    print()
    print(f"||x - x_ref||_inf = {float(np.max(np.abs(result.x - x_ref))):.2e}")
    print(f"|obj - obj_ref|   = {abs(result.objective - obj_ref):.2e}")

    np.testing.assert_allclose(result.x, x_ref, atol=1e-4)
    np.testing.assert_allclose(result.objective, obj_ref, atol=1e-6)
    assert result.status == "optimal", result.status
    print("\nOK")


if __name__ == "__main__":
    main()
