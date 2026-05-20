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
  Cplus_open : IsOpen Cplus
  C_subset_Cplus : C ⊆ Cplus
  /-- Cone barrier parameter. -/
  ν : ℕ
  ν_pos : 0 < ν
  /-- The KKT operator from eq. (2.4) of the paper. -/
  Q : H → H
  /-- The barrier-gradient map (zero on `x`, `∇f*(y)` on `y`,
  `∇g*(τ) = -1/τ` on `τ`). -/
  φ : H → H
  /-- `Q` is continuously differentiable on `Cplus`. -/
  Q_contDiff : ContDiffOn ℝ 3 Q Cplus
  /-- **Proposition 1.** `Q` is monotone on `Cplus`. -/
  Q_monotone : ∀ u ∈ Cplus, ∀ v ∈ Cplus,
    0 ≤ inner ℝ (u - v) (Q u - Q v)
  /-- Euler-type identity used in the proof of Proposition 3 (sphericity):
  `⟨u, Q(u)⟩ = 0`. -/
  inner_u_Q : ∀ u ∈ Cplus, inner ℝ u (Q u) = (0 : ℝ)
  /-- Euler-type identity for `φ` (Proposition 3 proof):
  `⟨u, φ(u)⟩ = -(ν+1)`. -/
  inner_u_phi : ∀ u ∈ C, inner ℝ u (φ u) = -((ν : ℝ) + 1)
  /-- `φ` is continuously differentiable on `C`. -/
  phi_contDiff : ContDiffOn ℝ 3 φ C
  /-- The barrier-gradient map `φ` is monotone on `C`. This is a
  direct consequence of `F* = f* + g*` being convex (the gradient of
  a convex function is monotone) — strict convexity is built into the
  LHSCB definition. We record it as an `IrnSetup` hypothesis since the
  `LHSCB` interface in this first pass does not yet expose `F*` as a
  potential. -/
  phi_monotone : ∀ u ∈ C, ∀ v ∈ C,
    0 ≤ inner ℝ (u - v) (φ u - φ v)
  /-- The `W(u)⁻¹`-weighted norm `‖·‖_{W(u)⁻¹}`, where
  `W(u) = I + ∇²F*(u)`. Carried as a field to sidestep the
  linear-operator-inverse machinery; its required algebraic and
  bound properties are recorded below. -/
  normWinv : H → H → ℝ
  /-- `normWinv` is nonnegative. -/
  normWinv_nonneg : ∀ u v, 0 ≤ normWinv u v
  /-- `W(u) ⪰ I` implies `W(u)⁻¹ ⪯ I`, so the dual norm is bounded
  by the Euclidean norm. -/
  normWinv_le_norm : ∀ u v, normWinv u v ≤ ‖v‖
  /-- Triangle inequality. -/
  normWinv_triangle : ∀ u v w, normWinv u (v + w) ≤ normWinv u v + normWinv u w
  /-- Absolute homogeneity. -/
  normWinv_smul : ∀ u (r : ℝ) v, normWinv u (r • v) = |r| * normWinv u v
  /-- LHSCB gradient identity: `‖φ(u)‖²_{W(u)⁻¹} ≤ ν + 1`, hence
  `‖φ(u)‖_{W(u)⁻¹} ≤ √(ν+1)`. The bound is `√ν + 1 = √(ν+1)` because
  the τ-block contributes at most `1`. -/
  normWinv_phi_bound : ∀ u ∈ C, normWinv u (φ u) ≤ Real.sqrt ((ν : ℝ) + 1)
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
  /-- KKT decomposition: `Q u = M u - q(u) • e_τ` on `Cplus`. -/
  Q_decomposition : ∀ u ∈ Cplus, Q u = M u - q u • e_τ
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

end IrnSetup

end Irn
