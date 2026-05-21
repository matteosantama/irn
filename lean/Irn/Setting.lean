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
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
  -- Theorem 8 ingredients: explicit embedding structure.
  -- The KKT operator splits as `Q u = M u - q(u) • e_τ` where `M` is
  -- the linear (skew-off-diagonal) part of the embedding matrix, `e_τ`
  -- is the τ-direction unit vector, and `q(u) = x⊤Px/τ` is the
  -- rational correction.
  /-- The linear embedding map. -/
  M : H →L[ℝ] H
  /-- The τ-direction unit vector in `H = ℝⁿ × ℝᵐ × ℝ`. -/
  e_τ : H
  /-- The τ-component projection. -/
  tau_proj : H → ℝ
  /-- `tau_proj u > 0` on `Cplus`. -/
  tau_proj_pos : ∀ u ∈ Cplus, 0 < tau_proj u
  /-- `e_τ` is dual to `tau_proj`: `⟨u, e_τ⟩ = tau_proj u`. With the
  standard inner product on `H = ℝⁿ × ℝᵐ × ℝ` and `e_τ` the unit
  τ-vector, this identifies the τ-component with the τ-inner-product. -/
  inner_u_e_tau : ∀ u : H, inner ℝ u e_τ = tau_proj u
  /-- The user-supplied `ν`-LHSCB `f` on `K*`, lifted to a `ν`-LHSCB on
  `H` (extended trivially to the `x` and `τ` blocks). The combined
  `(ν+1)`-LHSCB `F = f + g` with `g(τ) = -log τ` is derived as
  `IrnSetup.F_lhscb` below. -/
  f_lhscb : LHSCB H ν
  /-- The user's barrier is finite on `C`. -/
  C_subset_f_domain : C ⊆ f_lhscb.domain
  /-- The IRN setup's `φ = ∇F*` decomposes as `∇f* + ∇g*` where
  `g(τ) = -log τ` gives `∇g*(τ) = -1/τ`. The g-component lifts to
  `(-1/tau_proj u) • e_τ` on `H`. -/
  phi_eq_grad : ∀ u ∈ C,
    φ u = f_lhscb.grad u + (-1 / tau_proj u) • e_τ
  /-- LHSCB gradient identity: `‖φ(u)‖²_{W(u)⁻¹} ≤ ν + 1`, hence
  `‖φ(u)‖_{W(u)⁻¹} ≤ √(ν+1)`. Specific to the combined `F = f + g`
  Hessian; does not decompose from the parts. -/
  normWinv_phi_bound : ∀ u ∈ C, normWinv u (φ u) ≤ Real.sqrt ((ν : ℝ) + 1)
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
  /-- **Euler identity for the linear part of `Q`.** The skew off-diagonal
  blocks of `M` cancel pairwise in `⟨u, M u⟩`, leaving only the primal
  quadratic `x⊤Px = Px_bilinform(u, u)`. -/
  inner_u_M : ∀ u : H, inner ℝ u (M u) = Px_bilinform u u
  /-- **Structural form of `Q`.** Combines the matrix decomposition
  `Q u = M u - q(u) • e_τ` with the rational correction
  `q(u) = x⊤Px / τ = Px_bilinform(u, u) / tau_proj(u)` (eq. (2.4)). -/
  Q_eq : ∀ u ∈ Cplus,
    Q u = M u - (Px_bilinform u u / tau_proj u) • e_τ
  /-- **τ-rescaled PSD identity for `P`.** Since `Px(u, v) = x_u⊤ P x_v`
  with `P ⪰ 0`, the rescaled quadratic form
  `(τ_v x_u - τ_u x_v)⊤ P (τ_v x_u - τ_u x_v) ≥ 0` is just PSD-ness of
  `P` after a τ-rescaling. This single algebraic fact (expanded as a
  polynomial in `Px(·,·)` and `tau_proj`) drives the monotonicity of
  `Q` on `Cplus`. -/
  Px_quad_form_psd : ∀ u v : H,
    0 ≤ tau_proj v ^ 2 * Px_bilinform u u
        - 2 * tau_proj u * tau_proj v * Px_bilinform u v
        + tau_proj u ^ 2 * Px_bilinform v v
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

/-- **Euler-type identity for `Q`.** `⟨u, Q(u)⟩ = 0` on `Cplus`. The
matrix part contributes `Px(u, u)` (skew off-diagonals cancel) and the
rational correction contributes `-(Px(u, u)/τ) · τ = -Px(u, u)`, which
cancels. -/
theorem inner_u_Q (u : H) (hu : u ∈ 𝓢.Cplus) :
    inner ℝ u (𝓢.Q u) = (0 : ℝ) := by
  have hτ : 0 < 𝓢.tau_proj u := 𝓢.tau_proj_pos u hu
  have hτ_ne : 𝓢.tau_proj u ≠ 0 := ne_of_gt hτ
  rw [𝓢.Q_eq u hu, inner_sub_right, inner_smul_right, 𝓢.inner_u_M,
      𝓢.inner_u_e_tau]
  field_simp
  ring

/-- **Proposition 1 (Monotonicity of `Q`).** Direct calculation gives
`⟨u₁ - u₂, Q(u₁) - Q(u₂)⟩ = τ₁τ₂(z₁ - z₂)⊤ P (z₁ - z₂) ≥ 0`. The
τ-rescaling is captured by `Px_quad_form_psd`. -/
theorem Q_monotone (u : H) (hu : u ∈ 𝓢.Cplus) (v : H) (hv : v ∈ 𝓢.Cplus) :
    0 ≤ inner ℝ (u - v) (𝓢.Q u - 𝓢.Q v) := by
  have hτu : 0 < 𝓢.tau_proj u := 𝓢.tau_proj_pos u hu
  have hτv : 0 < 𝓢.tau_proj v := 𝓢.tau_proj_pos v hv
  have hτu_ne : 𝓢.tau_proj u ≠ 0 := ne_of_gt hτu
  have hτv_ne : 𝓢.tau_proj v ≠ 0 := ne_of_gt hτv
  have hτuv : 0 < 𝓢.tau_proj u * 𝓢.tau_proj v := mul_pos hτu hτv
  rw [𝓢.Q_eq u hu, 𝓢.Q_eq v hv]
  -- Regroup the difference as `M(u - v) - (q(u) - q(v)) • e_τ`.
  have h_arrange :
      𝓢.M u - (𝓢.Px_bilinform u u / 𝓢.tau_proj u) • 𝓢.e_τ -
        (𝓢.M v - (𝓢.Px_bilinform v v / 𝓢.tau_proj v) • 𝓢.e_τ) =
      𝓢.M (u - v) -
        ((𝓢.Px_bilinform u u / 𝓢.tau_proj u) -
          (𝓢.Px_bilinform v v / 𝓢.tau_proj v)) • 𝓢.e_τ := by
    rw [map_sub 𝓢.M]
    module
  rw [h_arrange, inner_sub_right, inner_smul_right, 𝓢.inner_u_M (u - v)]
  -- Expand `Px(u - v, u - v)` bilinearly.
  have h_Px_expand :
      𝓢.Px_bilinform (u - v) (u - v) =
        𝓢.Px_bilinform u u - 2 * 𝓢.Px_bilinform u v + 𝓢.Px_bilinform v v := by
    have h1 : 𝓢.Px_bilinform (u - v) = 𝓢.Px_bilinform u - 𝓢.Px_bilinform v :=
      map_sub _ _ _
    rw [h1]
    simp only [ContinuousLinearMap.sub_apply]
    rw [show (𝓢.Px_bilinform u) (u - v) =
              𝓢.Px_bilinform u u - 𝓢.Px_bilinform u v from map_sub _ _ _,
        show (𝓢.Px_bilinform v) (u - v) =
              𝓢.Px_bilinform v u - 𝓢.Px_bilinform v v from map_sub _ _ _,
        𝓢.Px_symm v u]
    ring
  rw [h_Px_expand]
  -- `⟨u - v, e_τ⟩ = τ_u - τ_v`.
  have h_inner_etau : inner ℝ (u - v) 𝓢.e_τ = 𝓢.tau_proj u - 𝓢.tau_proj v := by
    rw [inner_sub_left, 𝓢.inner_u_e_tau, 𝓢.inner_u_e_tau]
  rw [h_inner_etau]
  -- Rewrite as `(τ-rescaled PSD form) / (τ_u τ_v)` and apply `Px_quad_form_psd`.
  have h_psd :
      0 ≤ 𝓢.tau_proj v ^ 2 * 𝓢.Px_bilinform u u -
          2 * 𝓢.tau_proj u * 𝓢.tau_proj v * 𝓢.Px_bilinform u v +
          𝓢.tau_proj u ^ 2 * 𝓢.Px_bilinform v v :=
    𝓢.Px_quad_form_psd u v
  have h_id :
      𝓢.Px_bilinform u u - 2 * 𝓢.Px_bilinform u v + 𝓢.Px_bilinform v v -
          (𝓢.Px_bilinform u u / 𝓢.tau_proj u -
            𝓢.Px_bilinform v v / 𝓢.tau_proj v) *
              (𝓢.tau_proj u - 𝓢.tau_proj v) =
        (𝓢.tau_proj v ^ 2 * 𝓢.Px_bilinform u u -
          2 * 𝓢.tau_proj u * 𝓢.tau_proj v * 𝓢.Px_bilinform u v +
          𝓢.tau_proj u ^ 2 * 𝓢.Px_bilinform v v) /
          (𝓢.tau_proj u * 𝓢.tau_proj v) := by
    field_simp
    ring
  rw [h_id]
  exact div_nonneg h_psd (le_of_lt hτuv)

/-- `Cplus` is open: it equals the preimage of `(0, ∞)` under the
continuous linear functional `tau_proj_linear`. -/
theorem Cplus_open : IsOpen 𝓢.Cplus := by
  have h_eq : 𝓢.Cplus = 𝓢.tau_proj_linear ⁻¹' Set.Ioi 0 := by
    ext u
    refine ⟨fun hu => ?_, fun hu => ?_⟩
    · show 0 < 𝓢.tau_proj_linear u
      rw [𝓢.tau_proj_linear_eq u]; exact 𝓢.tau_proj_pos u hu
    · refine 𝓢.Cplus_of_tau_proj_pos u ?_
      have : 0 < 𝓢.tau_proj_linear u := hu
      rw [𝓢.tau_proj_linear_eq u] at this; exact this
  rw [h_eq]
  exact 𝓢.tau_proj_linear.continuous.isOpen_preimage _ isOpen_Ioi

/-- The concrete `1`-LHSCB `g(τ) = -log τ` lifted to `H`. The gradient
is `(-1/tau_proj u) • e_τ`; the Euler identity `⟨u, ∇g(u)⟩ = -1` uses
`inner_u_e_tau`; monotonicity uses `(τ_u - τ_v)² / (τ_u τ_v) ≥ 0`. -/
noncomputable def g_lhscb : LHSCB H 1 where
  f := fun u => -Real.log (𝓢.tau_proj u)
  grad := fun u => (-1 / 𝓢.tau_proj u) • 𝓢.e_τ
  domain := 𝓢.Cplus
  domain_open := 𝓢.Cplus_open
  euler := by
    intros u hu
    have hτ : 0 < 𝓢.tau_proj u := 𝓢.tau_proj_pos u hu
    have hτ_ne : 𝓢.tau_proj u ≠ 0 := ne_of_gt hτ
    rw [inner_smul_right, 𝓢.inner_u_e_tau]
    push_cast
    field_simp
  grad_monotone := by
    intros u hu v hv
    have hτu : 0 < 𝓢.tau_proj u := 𝓢.tau_proj_pos u hu
    have hτv : 0 < 𝓢.tau_proj v := 𝓢.tau_proj_pos v hv
    have hτu_ne : 𝓢.tau_proj u ≠ 0 := ne_of_gt hτu
    have hτv_ne : 𝓢.tau_proj v ≠ 0 := ne_of_gt hτv
    have h_sub_smul :
        (-1 / 𝓢.tau_proj u) • 𝓢.e_τ - (-1 / 𝓢.tau_proj v) • 𝓢.e_τ =
        ((-1 / 𝓢.tau_proj u) - (-1 / 𝓢.tau_proj v)) • 𝓢.e_τ := by
      rw [sub_smul]
    rw [h_sub_smul, inner_smul_right]
    have h_inner :
        inner ℝ (u - v) 𝓢.e_τ = 𝓢.tau_proj u - 𝓢.tau_proj v := by
      rw [inner_sub_left, 𝓢.inner_u_e_tau, 𝓢.inner_u_e_tau]
    rw [h_inner]
    have h_factor :
        ((-1 / 𝓢.tau_proj u) - (-1 / 𝓢.tau_proj v)) *
            (𝓢.tau_proj u - 𝓢.tau_proj v) =
        (𝓢.tau_proj u - 𝓢.tau_proj v) ^ 2 /
            (𝓢.tau_proj u * 𝓢.tau_proj v) := by
      field_simp
      ring
    rw [h_factor]
    positivity

/-- The combined `(ν+1)`-LHSCB `F = f + g` driving the IRN central path. -/
noncomputable def F_lhscb : LHSCB H (𝓢.ν + 1) :=
  𝓢.f_lhscb.add 𝓢.g_lhscb

/-- `C ⊆ F_lhscb.domain = f_lhscb.domain ∩ Cplus`. -/
theorem C_subset_F_domain : 𝓢.C ⊆ 𝓢.F_lhscb.domain := fun _ hu =>
  ⟨𝓢.C_subset_f_domain hu, 𝓢.C_subset_Cplus hu⟩

/-- The IRN setup's `φ` equals the combined LHSCB gradient on `C`. -/
theorem phi_eq_F_grad (u : H) (hu : u ∈ 𝓢.C) :
    𝓢.φ u = 𝓢.F_lhscb.grad u := by
  show 𝓢.φ u = (𝓢.f_lhscb.add 𝓢.g_lhscb).grad u
  rw [LHSCB.add_grad]
  exact 𝓢.phi_eq_grad u hu

/-- **Euler-type identity for `φ`** (Proposition 3 proof):
`⟨u, φ(u)⟩ = -(ν+1)`. Derived from the LHSCB Euler identity for
`F = f + g` (a `(ν+1)`-LHSCB). -/
theorem inner_u_phi (u : H) (hu : u ∈ 𝓢.C) :
    inner ℝ u (𝓢.φ u) = -((𝓢.ν : ℝ) + 1) := by
  rw [𝓢.phi_eq_F_grad u hu, 𝓢.F_lhscb.euler u (𝓢.C_subset_F_domain hu)]
  push_cast
  ring

/-- **Monotonicity of `φ`** on `C`. The gradient of a convex function
is monotone; here `F = f + g` is convex. -/
theorem phi_monotone (u : H) (hu : u ∈ 𝓢.C) (v : H) (hv : v ∈ 𝓢.C) :
    0 ≤ inner ℝ (u - v) (𝓢.φ u - 𝓢.φ v) := by
  rw [𝓢.phi_eq_F_grad u hu, 𝓢.phi_eq_F_grad v hv]
  exact 𝓢.F_lhscb.grad_monotone u (𝓢.C_subset_F_domain hu) v
    (𝓢.C_subset_F_domain hv)

end IrnSetup

end Irn
