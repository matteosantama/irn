"""Interior Riemannian Newton solver for convex QPs over the non-negative orthant.

Solves

    min  1/2 x^T P x + c^T x
    s.t. A x + s = b,  s >= 0,

with P symmetric positive semidefinite. The solver follows the
Riemannian Josephy--Newton method (Variant A: sphericity-enforcing) on
the homogeneous embedding of the central path, restricted to the cone
K = R^m_+.

For K = R^m_+ the LHSCB is the log-barrier f^*(y) = -sum_i log y_i with
nu = m, grad f^*(y) = -1/y, and Hessian diag(1/y^2). Consequently the
preconditioner H_k = mu I + mu nabla^2 F^*(u_k) is diagonal and the
quasi-definite linear system H_k + M is sparse with the same nonzero
pattern as the bordered KKT matrix of the original QP.

Inputs P and A are scipy sparse arrays/matrices (dense ndarrays are also
accepted and auto-converted). The single per-iteration sparse LU
factorisation is shared across the three back-substitutions
parametrising the lambda-family of Newton iterates.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal, Union

import numpy as np
import scipy.sparse as sp
from scipy.sparse.linalg import splu

ArrayLike = Union[np.ndarray, sp.sparray, sp.spmatrix]

Status = Literal["optimal", "max_iterations", "numerical_failure"]


@dataclass(frozen=True)
class Result:
    """Output of :func:`solve`."""

    x: np.ndarray
    y: np.ndarray
    s: np.ndarray
    status: Status
    iterations: int
    mu: float
    residual: float
    objective: float


def solve(
    P: ArrayLike,
    A: ArrayLike,
    b: np.ndarray,
    c: np.ndarray,
    *,
    max_iter: int = 100,
    max_inner: int = 20,
    tol: float = 1e-8,
    sigma: float = 0.3,
    interior_safeguard: float = 0.99,
    mu_floor: float = 1e-14,
    verbose: bool = False,
) -> Result:
    """Solve a convex QP over the non-negative orthant.

    Parameters
    ----------
    P : (n, n) scipy sparse array/matrix, or dense ndarray
        Symmetric positive semidefinite quadratic cost. Dense input is
        converted to CSC sparse internally.
    A : (m, n) scipy sparse array/matrix, or dense ndarray
        Constraint matrix.
    b : (m,) array_like
        Constraint right-hand side.
    c : (n,) array_like
        Linear cost vector.
    max_iter : int
        Maximum number of outer (mu-reduction) iterations.
    max_inner : int
        Maximum number of Riemannian Newton steps per outer iteration.
    tol : float
        KKT tolerance for declaring optimality.
    sigma : float
        Multiplicative factor by which mu is reduced at each outer
        iteration.
    interior_safeguard : float
        Safety factor in (0, 1) for the cone-feasibility step length.
    mu_floor : float
        Lower bound on mu; below this the outer loop terminates.
    verbose : bool
        Print per-iteration progress.

    Notes
    -----
    Termination is based on the KKT residuals of the recovered
    primal-dual pair (xbar, ybar) := (x/tau, y/tau):
      primal infeasibility = max(0, -min(b - A xbar))
      dual infeasibility   = ||P xbar + A^T ybar + c||_inf
      duality gap          = |xbar^T P xbar + c^T xbar + b^T ybar|
    All three must be below `tol` for the solver to declare optimality.
    """
    P_sp = _as_csc(P, "P")
    A_sp = _as_csc(A, "A")
    b_arr = np.asarray(b, dtype=float).ravel()
    c_arr = np.asarray(c, dtype=float).ravel()

    m, n = A_sp.shape
    if P_sp.shape != (n, n):
        raise ValueError(f"P must be ({n}, {n}); got {P_sp.shape}")
    if b_arr.shape != (m,):
        raise ValueError(f"b must have length {m}; got {b_arr.shape}")
    if c_arr.shape != (n,):
        raise ValueError(f"c must have length {n}; got {c_arr.shape}")

    nu = m
    r = np.sqrt(nu + 1.0)

    u = _initialise(n, m, b_arr, r)
    mu = 1.0
    residual = float("inf")
    status: Status = "max_iterations"
    iterations = 0

    for k in range(max_iter):
        iterations = k + 1
        inner_residual = float("inf")
        inner_failed = False
        j = 0
        for j in range(max_inner):
            try:
                u_new = _riemannian_step(
                    u, mu, P_sp, A_sp, b_arr, c_arr,
                    n, m, nu, r, interior_safeguard,
                )
            except _NewtonFailed as exc:
                if verbose:
                    print(f"  inner failure at j={j}, mu={mu:.2e}: {exc}")
                inner_failed = True
                break
            step = float(np.linalg.norm(u_new - u))
            u = u_new
            if step < 1e-14:
                break
            T = _t_mu(u, mu, P_sp, A_sp, b_arr, c_arr, n, m)
            inner_residual = float(np.linalg.norm(T, ord=np.inf))
            if inner_residual < 1e-10 * max(mu, 1.0):
                break
        residual = inner_residual

        kkt = _kkt_residual(u, P_sp, A_sp, b_arr, c_arr, n, m)
        if verbose:
            tau = float(u[n + m])
            print(
                f"iter={k:3d}  mu={mu:.2e}  inner={j+1:2d}  "
                f"||T||={inner_residual:.2e}  tau={tau:.3e}  "
                f"prim={kkt['primal']:.2e}  dual={kkt['dual']:.2e}  "
                f"gap={kkt['gap']:.2e}"
            )

        if _kkt_optimal(kkt, tol):
            status = "optimal"
            break

        if inner_failed:
            status = "numerical_failure"
            break

        if mu < mu_floor:
            break
        mu *= sigma

    x, y, tau = _split(u, n, m)
    if tau > 0:
        x_bar = x / tau
        y_bar = y / tau
    else:
        x_bar = x.copy()
        y_bar = y.copy()
    s_bar = b_arr - A_sp @ x_bar
    obj = 0.5 * x_bar @ (P_sp @ x_bar) + c_arr @ x_bar

    return Result(
        x=x_bar,
        y=y_bar,
        s=s_bar,
        status=status,
        iterations=iterations,
        mu=mu,
        residual=residual,
        objective=float(obj),
    )


# ----------------------------------------------------------------------
#  Internals
# ----------------------------------------------------------------------


class _NewtonFailed(Exception):
    pass


def _as_csc(M, name):
    """Convert sparse-or-dense input to CSC sparse array."""
    if sp.issparse(M):
        return M.tocsc()
    arr = np.atleast_2d(np.asarray(M, dtype=float))
    return sp.csc_array(arr)


def _split(u, n, m):
    return u[:n], u[n : n + m], float(u[n + m])


def _initialise(n, m, b, r):
    """Sphere-projected Jordan-quadratic initialiser for the orthant."""
    y0 = 0.5 * (-b + np.sqrt(b * b + 4.0))
    u = np.concatenate([np.zeros(n), y0, [1.0]])
    norm = float(np.linalg.norm(u))
    return u * (r / norm)


def _kkt_residual(u, P, A, b, c, n, m):
    """KKT residuals at the recovered primal-dual point."""
    x, y, tau = _split(u, n, m)
    if tau <= 0:
        return {"primal": float("inf"), "dual": float("inf"), "gap": float("inf")}
    xb = x / tau
    yb = y / tau
    sb = b - A @ xb
    primal = float(max(0.0, -float(np.min(sb))))
    dual_res = P @ xb + A.T @ yb + c
    dual = float(np.linalg.norm(dual_res, ord=np.inf))
    Pxb = P @ xb
    gap = abs(float(xb @ Pxb + c @ xb + b @ yb))
    return {"primal": primal, "dual": dual, "gap": gap}


def _kkt_optimal(kkt, tol):
    return max(kkt["primal"], kkt["dual"], kkt["gap"]) < tol


def _t_mu(u, mu, P, A, b, c, n, m):
    """Evaluate T_mu(u) = Q(u) + mu u + mu phi(u) for the orthant."""
    x, y, tau = _split(u, n, m)
    Px = P @ x
    T = np.empty(n + m + 1)
    T[:n] = Px + A.T @ y + c * tau + mu * x
    T[n : n + m] = -(A @ x) + b * tau + mu * y - mu / y
    T[n + m] = -(c @ x) - (b @ y) - (x @ Px) / tau + mu * tau - mu / tau
    return T


def _assemble_hm(P, A, b, c, mu, y, n, m):
    """Assemble the quasi-definite system matrix H_k + M as CSC sparse.

    Structure:
        [ P + mu I_n   A^T          c   ]
        [ -A           mu I + diag  b   ]
        [ -c^T         -b^T         mu  ]
    """
    P_plus = P + mu * sp.eye_array(n, format="csc")
    diag_block = sp.diags_array(mu + mu / (y * y), format="csc")
    # Reshape b, c into 2D so block_array sees them as blocks.
    c_col = c[:, None]
    b_col = b[:, None]
    nc_row = (-c)[None, :]
    nb_row = (-b)[None, :]
    mu_1x1 = np.array([[mu]])
    HM = sp.block_array(
        [
            [P_plus, A.T, c_col],
            [-A, diag_block, b_col],
            [nc_row, nb_row, mu_1x1],
        ],
        format="csc",
    )
    return HM


def _riemannian_step(u, mu, P, A, b, c, n, m, nu, r, interior_safeguard):
    """One Riemannian Josephy--Newton step (Variant A: sphericity)."""
    x, y, tau = _split(u, n, m)
    size = n + m + 1

    HM = _assemble_hm(P, A, b, c, mu, y, n, m)

    # rhs_h = H_k u_k - h(u_k) = (0, 2 mu / y, 0) for the orthant
    rhs_h = np.zeros(size)
    rhs_h[n : n + m] = 2.0 * mu / y
    e_tau = np.zeros(size)
    e_tau[-1] = 1.0

    try:
        lu = splu(HM)
    except RuntimeError as exc:
        raise _NewtonFailed(f"sparse LU failed: {exc}") from exc

    # Solve the three RHS sharing the factorisation.
    RHS = np.column_stack([rhs_h, e_tau, u])
    W = lu.solve(RHS)
    w0, w1, w2 = W[:, 0], W[:, 1], W[:, 2]

    Pw1x = P @ w1[:n]
    alpha = float(w1[n + m] - w1[:n] @ Pw1x)
    Pw2x = P @ w2[:n]
    beta_prime = float(-w2[n + m] + 2.0 * w2[:n] @ Pw1x)

    def eval_lambda(lam):
        w0x = w0[:n] - lam * w2[:n]
        w0tau = float(w0[n + m] - lam * w2[n + m])
        Pw0x = P @ w0x
        beta = w0tau - 2.0 * float(w0x @ Pw1x)
        gamma = -float(w0x @ Pw0x) - mu

        if abs(alpha) < 1e-14:
            if abs(beta) < 1e-14:
                raise _NewtonFailed("degenerate theta quadratic")
            theta = -gamma / beta
        else:
            disc = beta * beta - 4.0 * alpha * gamma
            if disc < 0:
                if disc > -1e-12 * max(1.0, abs(beta * beta)):
                    disc = 0.0
                else:
                    raise _NewtonFailed(
                        f"negative discriminant {disc:.2e} in theta quadratic"
                    )
            sqrt_disc = np.sqrt(disc)
            theta_p = (-beta + sqrt_disc) / (2.0 * alpha)
            theta_m = (-beta - sqrt_disc) / (2.0 * alpha)
            tau_p = w0tau + theta_p * w1[n + m]
            tau_m = w0tau + theta_m * w1[n + m]
            if tau_p > 0 and (tau_m <= 0 or theta_p > 0):
                theta = theta_p
            elif tau_m > 0:
                theta = theta_m
            else:
                raise _NewtonFailed("no theta root yields positive tau")

        u_l = w0 - lam * w2 + theta * w1
        phi = float(u_l @ u_l - (nu + 1.0))

        gamma_prime = 2.0 * float(w0x @ Pw2x)
        denom = 2.0 * alpha * theta + beta
        if abs(denom) < 1e-14:
            theta_prime = 0.0
        else:
            theta_prime = -(beta_prime * theta + gamma_prime) / denom
        u_l_prime = -w2 + theta_prime * w1
        dphi = 2.0 * float(u_l @ u_l_prime)
        return phi, dphi, u_l

    lam = 0.0
    phi, dphi, u_l = eval_lambda(lam)
    for _ in range(25):
        if abs(phi) < 1e-12:
            break
        if abs(dphi) < 1e-14:
            break
        step = phi / dphi
        lam -= step
        phi, dphi, u_l = eval_lambda(lam)
        if abs(step) < 1e-13:
            break

    dy = u_l[n : n + m] - y
    dtau = float(u_l[n + m] - tau)
    alpha_step = 1.0
    neg_y = dy < 0
    if np.any(neg_y):
        alpha_step = min(alpha_step, float(np.min(-y[neg_y] / dy[neg_y])))
    if dtau < 0:
        alpha_step = min(alpha_step, -tau / dtau)
    if alpha_step < 1.0:
        alpha_step *= interior_safeguard

    mix = (1.0 - alpha_step) * u + alpha_step * u_l
    norm = float(np.linalg.norm(mix))
    if norm == 0.0:
        raise _NewtonFailed("zero chord after step length")
    return r * mix / norm
