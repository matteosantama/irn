/-
# Setting (paper §1–§2.1)

The homogeneous embedding of a conic quadratic program, the KKT
operator `Q`, and its monotonicity (Proposition 1).

We abstract the ambient finite-dimensional real Hilbert space `H`
(which the paper takes to be `ℝⁿ × ℝᵐ × ℝ`) and bundle the embedding
data into an `IrnSetup` structure. Fundamental properties that the
paper derives from the concrete block structure of `M` — monotonicity
of `Q`, the Euler identity `⟨u, Q(u)⟩ = 0`, and so on — appear as
fields of `IrnSetup`, since we do not carry the explicit matrix data.

Paper references:
* Definition of `Q` — eq. (2.4)
* Proposition 1 — `IrnSetup.Q_monotone`
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Irn.Barriers

namespace Irn

open scoped InnerProductSpace

/--
Data and hypotheses of the homogeneous embedding of a conic quadratic
program, abstracted over a finite-dimensional real Hilbert space `H`.

The fields bundle:

* the cones `C ⊆ Cplus`,
* the cone barrier parameter `ν`,
* the KKT operator `Q`,
* the barrier-gradient map `φ`,

together with the properties the paper proves about them in §1–§2.1.
-/
structure IrnSetup (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] where
  /-- The proper cone `C = ℝⁿ × K* × ℝ₊` in `H`. -/
  C : Set H
  /-- The relaxed monotonicity domain `Cplus = ℝⁿ × ℝᵐ × ℝ₊₊`. -/
  Cplus : Set H
  C_subset_Cplus : C ⊆ Cplus
  /-- Cone barrier parameter. -/
  ν : ℕ
  ν_pos : 0 < ν
  /-- The KKT operator from eq. (2.4) of the paper. -/
  Q : H → H
  /-- The barrier-gradient map (zero on `x`, `∇f*(y)` on `y`,
  `∇g*(τ) = -1/τ` on `τ`). -/
  φ : H → H
  /-- **Proposition 1.** `Q` is monotone on `Cplus`. -/
  Q_monotone : ∀ u ∈ Cplus, ∀ v ∈ Cplus,
    0 ≤ inner ℝ (u - v) (Q u - Q v)
  /-- Euler-type identity used in the proof of Proposition 3 (sphericity):
  `⟨u, Q(u)⟩ = 0`. -/
  inner_u_Q : ∀ u ∈ Cplus, inner ℝ u (Q u) = (0 : ℝ)
  /-- The combined `(ν+1)`-LHSCB `F = f + g`, where `f` is the
  user-supplied `ν`-LHSCB on `K*` and `g(τ) = -log τ` is the standard
  `1`-LHSCB on `ℝ_++`. The paper's `φ = ∇F*` factors through this
  bundle via `phi_eq_grad`; the three φ-consequences used downstream
  (Euler, monotonicity, dual-norm bound) are derived as theorems below
  rather than carried as separate `IrnSetup` fields. -/
  F_lhscb : LHSCB H (ν + 1)
  /-- The IRN setup's φ is the LHSCB gradient on `C`. -/
  phi_eq_grad : ∀ u ∈ C, φ u = F_lhscb.grad u
  /-- The barrier is finite on `C`. -/
  C_subset_domain : C ⊆ F_lhscb.domain
  /-- The `W(u)⁻¹`-weighted norm `‖·‖_{W(u)⁻¹}`, where
  `W(u) = I + ∇²F*(u)`. Carried as a field to sidestep the
  linear-operator-inverse machinery; its required algebraic and
  bound properties are recorded below. -/
  normWinv : H → H → ℝ
  /-- `normWinv` agrees with the LHSCB dual norm, so the LHSCB
  gradient bound transports to `‖φ(u)‖_{W(u)⁻¹} ≤ √(ν+1)`. -/
  normWinv_eq_dualNorm : ∀ u v, normWinv u v = F_lhscb.dualNorm u v
  /-- `normWinv` is nonnegative. -/
  normWinv_nonneg : ∀ u v, 0 ≤ normWinv u v
  /-- `W(u) ⪰ I` implies `W(u)⁻¹ ⪯ I`, so the dual norm is bounded
  by the Euclidean norm. -/
  normWinv_le_norm : ∀ u v, normWinv u v ≤ ‖v‖
  /-- Triangle inequality. -/
  normWinv_triangle : ∀ u v w, normWinv u (v + w) ≤ normWinv u v + normWinv u w
  /-- Absolute homogeneity. -/
  normWinv_smul : ∀ u (r : ℝ) v, normWinv u (r • v) = |r| * normWinv u v
  -- Theorem 8 ingredients: explicit embedding structure.
  -- The KKT operator splits as `Q u = M u - q(u) • e_τ` where `M` is
  -- the linear (skew-off-diagonal) part of the embedding matrix, `e_τ`
  -- is the τ-direction unit vector, and `q(u) = x⊤Px/τ` is the
  -- rational correction.
  /-- The linear embedding map. -/
  M : H →L[ℝ] H
  /-- The τ-direction unit vector in `H = ℝⁿ × ℝᵐ × ℝ`. -/
  e_τ : H
  /-- The rational correction `q(u) = x⊤Px/τ`. -/
  q : H → ℝ
  /-- The τ-component projection. -/
  tau_proj : H → ℝ
  /-- `tau_proj u > 0` on `Cplus`. -/
  tau_proj_pos : ∀ u ∈ Cplus, 0 < tau_proj u
  -- The Riemannian Josephy–Newton corrector.
  /-- The Hessian preconditioner `H_k = ∇h(u_k) = μI + μ∇²F*(u_k)`. -/
  hessian_h : ℝ → H → H →L[ℝ] H
  /-- The Riemannian Josephy–Newton corrector (Variant A). Computed via
  Theorem 8 (`Irn.resolvent_closed_form`) at the `λ`-shifted input of
  eq. (5.4); recorded as a function field with properties recorded as
  theorem statements (with `sorry` proofs) in `Irn.PathFollowing`. -/
  rjnStep : ℝ → H → H
  /-- The sphere-constraint Lagrange multiplier (Proposition 11). -/
  rjnLambda : ℝ → H → ℝ
  -- Theorem 8 Part 2 ingredients: linearity, bilinearity, invertibility.
  /-- `tau_proj` as a continuous linear functional. -/
  tau_proj_linear : H →L[ℝ] ℝ
  /-- The continuous linear functional agrees with the scalar projection. -/
  tau_proj_linear_eq : ∀ u, tau_proj_linear u = tau_proj u
  /-- The bilinear form `B_P(u, v) = u_x⊤Pv_x` from the primal quadratic. -/
  Px_bilinform : H →L[ℝ] H →L[ℝ] ℝ
  /-- `B_P` is symmetric. -/
  Px_symm : ∀ u v, Px_bilinform u v = Px_bilinform v u
  /-- The continuous linear equivalence `H_k + M`. The matrix `H_k + M`
  is invertible because its symmetric part is positive definite. -/
  hessian_plus_M : ℝ → H → (H ≃L[ℝ] H)
  /-- The equivalence coincides with `hessian_h μ u + M` pointwise. -/
  hessian_plus_M_eq : ∀ μ u v,
    (hessian_plus_M μ u : H →L[ℝ] H) v = hessian_h μ u v + M v
  /-- Reverse of `tau_proj_pos`: positive `tau_proj` implies `Cplus`. -/
  Cplus_of_tau_proj_pos : ∀ u : H, 0 < tau_proj u → u ∈ Cplus
  -- Proposition 11 ingredients: `rjnLambda` vanishes at the central path
  -- and is continuous there.
  /-- `rjnLambda μ` evaluates to `0` at central-path points (eq. `λ_k = 0`
  when `u_k = u*(μ)` from Proposition 11's order bound). The
  central-path condition `Q u + μ•u + μ•φ u = 0` is the unfolding of
  `T μ u = 0` in `IrnSetup` primitives. -/
  rjnLambda_at_central : ∀ μ : ℝ, ∀ u : H, 0 < μ → u ∈ C →
    Q u + μ • u + μ • φ u = 0 → rjnLambda μ u = 0
  /-- `rjnLambda μ` is continuous at the central-path point — the
  remaining content of Proposition 11 (the smooth-branch conclusion of
  the implicit function theorem). -/
  rjnLambda_continuousAt_central : ∀ μ : ℝ, ∀ u : H, 0 < μ → u ∈ C →
    Q u + μ • u + μ • φ u = 0 → ContinuousAt (rjnLambda μ) u
  -- Variant A invariance of the corrector. These two fields encode the
  -- sphere + interior-cone preservation enforced by the augmented Newton
  -- inclusion of eq. (5.3).
  /-- The corrector preserves the squared-norm constraint `‖u‖² = ν+1`
  (the sphere `Sr`). -/
  rjnStep_norm_sq : ∀ μ : ℝ, ∀ u : H, 0 < μ →
    ‖u‖ ^ 2 = (ν : ℝ) + 1 → u ∈ C →
    ‖rjnStep μ u‖ ^ 2 = (ν : ℝ) + 1
  /-- The corrector preserves the interior cone `int C`. -/
  rjnStep_in_C : ∀ μ : ℝ, ∀ u : H, 0 < μ →
    ‖u‖ ^ 2 = (ν : ℝ) + 1 → u ∈ C →
    rjnStep μ u ∈ C
  /-- **Minty's theorem applied to `H_k + Ψ`.**

  The augmented Newton inclusion has a solution `(u, θ)`: there exists
  `u ∈ Cplus` and `θ > 0` satisfying both the augmented equation
  `(H_k + M) u = H_k z + θ • e_τ` and the scalar inclusion form
  `θ · tau_proj u = B_P(u, u) + μ`. This is Minty's theorem applied
  to the maximally monotone operator `H_k + Ψ`; recorded as a field
  because formalising maximally monotone set-valued operators is
  outside the scope of this pass. -/
  resolvent_exists : ∀ μ : ℝ, ∀ u_k z : H, 0 < μ →
    ∃ u : H, u ∈ Cplus ∧ ∃ θ : ℝ, 0 < θ ∧
      (hessian_h μ u_k + M) u = hessian_h μ u_k z + θ • e_τ ∧
      θ * tau_proj u = Px_bilinform u u + μ
  -- Theorem 12 / Lemma 15 ingredients: Newton-Kantorovich contractions.
  /-- **Lemma 15 (Hessian-norm Newton–Kantorovich).** On `Sr ∩ C`, one
  corrector step contracts `δ = normWinv(T)/μ` quadratically with basin
  radius `ρ_star` and rate `K_star`. Stated using the on-sphere identity
  `δ μ u = normWinv u (Q u + μ • u + μ • φ u) / μ` (the projector drops
  out by tangentiality). -/
  rjnStep_delta_contraction : ∃ ρ_star K_star : ℝ,
    0 < ρ_star ∧ ρ_star < 1 ∧ 1 ≤ K_star ∧
    ∀ μ : ℝ, 0 < μ → ∀ u : H, ‖u‖ ^ 2 = (ν : ℝ) + 1 → u ∈ C →
      normWinv u (Q u + μ • u + μ • φ u) / μ ≤ ρ_star →
      normWinv (rjnStep μ u)
          (Q (rjnStep μ u) + μ • (rjnStep μ u) + μ • φ (rjnStep μ u)) / μ ≤
        K_star * (normWinv u (Q u + μ • u + μ • φ u) / μ) ^ 2
  /-- **Theorem 12 (Euclidean Newton–Kantorovich).** Near each
  central-path point `u_star`, there is an open `U` containing `u_star`
  and a constant `K > 0` such that on `U ∩ Sr ∩ C` the corrector both
  stays in `U` (basin invariance) and contracts the Euclidean error
  quadratically. -/
  rjnStep_euclidean_basin : ∀ μ : ℝ, 0 < μ → ∀ u_star : H,
    u_star ∈ C → Q u_star + μ • u_star + μ • φ u_star = 0 →
    ∃ U : Set H, IsOpen U ∧ u_star ∈ U ∧ ∃ K : ℝ, 0 < K ∧
      (∀ u ∈ U, ‖u‖ ^ 2 = (ν : ℝ) + 1 → u ∈ C → rjnStep μ u ∈ U) ∧
      (∀ u ∈ U, ‖u‖ ^ 2 = (ν : ℝ) + 1 → u ∈ C →
         ‖rjnStep μ u - u_star‖ ≤ K * ‖u - u_star‖ ^ 2)

namespace IrnSetup

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  (𝓢 : IrnSetup H)

/-- Sphere radius `r = √(ν+1)`. -/
noncomputable def r : ℝ := Real.sqrt ((𝓢.ν : ℝ) + 1)

theorem r_sq : 𝓢.r ^ 2 = (𝓢.ν : ℝ) + 1 := by
  unfold IrnSetup.r
  exact Real.sq_sqrt (by positivity)

theorem r_pos : 0 < 𝓢.r := by
  unfold IrnSetup.r
  exact Real.sqrt_pos.mpr (by positivity)

/-- **Euler-type identity for `φ`** (Proposition 3 proof):
`⟨u, φ(u)⟩ = -(ν+1)`. Derived from the LHSCB Euler identity for
`F = f + g` (a `(ν+1)`-LHSCB). -/
theorem inner_u_phi (u : H) (hu : u ∈ 𝓢.C) :
    inner ℝ u (𝓢.φ u) = -((𝓢.ν : ℝ) + 1) := by
  rw [𝓢.phi_eq_grad u hu, 𝓢.F_lhscb.euler u (𝓢.C_subset_domain hu)]
  push_cast
  ring

/-- **Monotonicity of `φ`** on `C`. The gradient of a convex function
is monotone; here `F = f + g` is convex. -/
theorem phi_monotone (u : H) (hu : u ∈ 𝓢.C) (v : H) (hv : v ∈ 𝓢.C) :
    0 ≤ inner ℝ (u - v) (𝓢.φ u - 𝓢.φ v) := by
  rw [𝓢.phi_eq_grad u hu, 𝓢.phi_eq_grad v hv]
  exact 𝓢.F_lhscb.grad_monotone u (𝓢.C_subset_domain hu) v (𝓢.C_subset_domain hv)

/-- **LHSCB gradient bound** in the IRN dual norm:
`‖φ(u)‖_{W(u)⁻¹} ≤ √(ν+1)`. -/
theorem normWinv_phi_bound (u : H) (hu : u ∈ 𝓢.C) :
    𝓢.normWinv u (𝓢.φ u) ≤ Real.sqrt ((𝓢.ν : ℝ) + 1) := by
  rw [𝓢.normWinv_eq_dualNorm, 𝓢.phi_eq_grad u hu]
  have h := 𝓢.F_lhscb.dualNorm_grad_bound u (𝓢.C_subset_domain hu)
  push_cast at h
  exact h

end IrnSetup

end Irn
