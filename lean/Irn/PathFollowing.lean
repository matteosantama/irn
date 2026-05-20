/-
# Path-Following Complexity (paper §6)

The outer-loop analysis: tangentially-projected residual `tildeT`,
the on-sphere identity `P_u φ(u) = φ(u) + u`, the affine-in-`μ`
proximity-transfer identity, failure of Euclidean tolerances
(Proposition 12), the Hessian-norm proximity `δ`, the bounded
transfer constant (Lemma 13), the proximity transfer bound
(Lemma 14), the Hessian-norm quadratic contraction (Lemma 15), and
the polynomial complexity theorem (Theorem 16).

Paper references:
* Eq. (6.1) `P_u φ(u) = φ(u) + u`
* Eq. (6.3) transfer identity for `tildeT`
* Proposition 12 (failure of Euclidean tolerances)
* Remark 17 (power-law tolerances) — informal, no theorem
* Eq. (6.6) `W(u) = I + ∇²F*(u)`
* Eq. (6.7) Hessian-norm proximity `δ(u, μ)`
* Lemma 13 (bounded transfer constant)
* Lemma 14 (proximity transfer)
* Lemma 15 (Hessian-norm quadratic contraction)
* Theorem 16 (polynomial complexity)
-/

import Irn.RJN
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Irn

open scoped InnerProductSpace

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

variable (𝓢 : IrnSetup H)

/-- The tangentially-projected residual `tildeT_μ(u) = P_u T_μ(u)`. -/
noncomputable def tildeT (μ : ℝ) (u : H) : H := proj u (T 𝓢 μ u)

/-! ## §6.1 Proximity transfer identity. -/

/-- **Eq. (6.1).** On `Sr ∩ int C`, the projector simplifies to
`P_u φ(u) = φ(u) + u`. -/
theorem proj_phi_on_sphere {u : H}
    (hS : u ∈ sphere 𝓢) (hC : u ∈ 𝓢.C) :
    proj u (𝓢.φ u) = 𝓢.φ u + u := by
  unfold proj
  rw [𝓢.inner_u_phi u hC]
  have huu : ‖u‖ ^ 2 = (𝓢.ν : ℝ) + 1 := by
    have hnorm : ‖u‖ = 𝓢.r := hS
    rw [hnorm, 𝓢.r_sq]
  rw [huu]
  have hpos : (0 : ℝ) < (𝓢.ν : ℝ) + 1 := by positivity
  rw [neg_div, div_self (ne_of_gt hpos), neg_smul, one_smul, sub_neg_eq_add]

/-- **Eq. (6.3).** Affine-in-`μ` proximity transfer identity for
`tildeT`. On the sphere, `tildeT_μ(u) = T_μ(u)` (by tangentiality), so
this reduces to the vector identity
`T_{σμ}(u) = T_μ(u) - (1-σ)μ • (φ u + u)`. -/
theorem tildeT_transfer (μ σ : ℝ) (hμ : 0 < μ) (hσ : 0 < σ) {u : H}
    (hS : u ∈ sphere 𝓢) (hC : u ∈ 𝓢.C) :
    tildeT 𝓢 (σ * μ) u = tildeT 𝓢 μ u - ((1 - σ) * μ) • (𝓢.φ u + u) := by
  unfold tildeT
  rw [proj_of_orthogonal u _ (tangent_T 𝓢 (mul_pos hσ hμ) hS hC),
      proj_of_orthogonal u _ (tangent_T 𝓢 hμ hS hC)]
  unfold T
  module

/-! ## §6.2 Failure of Euclidean tolerances. -/

/-- The Euclidean transfer constant `R(u) = ‖φ(u) + u‖`. -/
noncomputable def R (u : H) : ℝ := ‖𝓢.φ u + u‖

/-- The identity `μ R(u*(μ)) = ‖Q(u*(μ))‖` from the proof of
Proposition 12. -/
theorem mu_R_eq_Q_norm {μ : ℝ} (hμ : 0 < μ) :
    μ * R 𝓢 (centralPathPoint 𝓢 μ hμ) =
      ‖𝓢.Q (centralPathPoint 𝓢 μ hμ)‖ := by
  set u := centralPathPoint 𝓢 μ hμ
  obtain ⟨_, hT⟩ := centralPathPoint_isCentralPathPoint 𝓢 μ hμ
  unfold T at hT
  unfold R
  have hT' : 𝓢.Q u + (μ • u + μ • 𝓢.φ u) = 0 := by
    rw [← add_assoc]; exact hT
  have hQ : 𝓢.Q u = -(μ • (𝓢.φ u + u)) := by
    have h1 : 𝓢.Q u = -(μ • u + μ • 𝓢.φ u) := add_eq_zero_iff_eq_neg.mp hT'
    rw [h1, smul_add, add_comm (μ • 𝓢.φ u)]
  rw [hQ, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hμ]

/-- **Proposition 12 (Failure of Euclidean tolerances).** For any
inner-loop tolerance function `f`, even a perfectly-centred iterate
`u_k = u*(μ_k)` requires `1 - σ_k = O(μ_k)` to keep the post-update
proximity inside any fixed-radius basin `ρ`. Polynomial complexity
`O(log(1/ε))` in the outer loop is unattainable with any Euclidean
tolerance.

We formalize the key identity at the central-path point: the
proximity `‖tildeT_{σμ}(u*(μ))‖ / (σμ)` equals
`(1 - σ)/σ · ‖Q(u*(μ))‖ / μ`, which is `Θ((1-σ)/μ)` since
`‖Q(u*(μ))‖ → ‖Q(u^∞)‖ > 0` in non-trivial instances. The
sub-linear schedule conclusion is left as a remark. -/
theorem euclidean_failure
    {μ : ℝ} (hμ : 0 < μ) {σ : ℝ} (hσ : 0 < σ) (hσ' : σ ≤ 1) :
    ‖tildeT 𝓢 (σ * μ) (centralPathPoint 𝓢 μ hμ)‖ / (σ * μ) =
      ((1 - σ) / σ) * (‖𝓢.Q (centralPathPoint 𝓢 μ hμ)‖ / μ) := by
  set u := centralPathPoint 𝓢 μ hμ
  obtain ⟨hC, hT⟩ := centralPathPoint_isCentralPathPoint 𝓢 μ hμ
  have hS : u ∈ sphere 𝓢 := by
    show ‖u‖ = 𝓢.r
    have h1 : ‖u‖ ^ 2 = (𝓢.ν : ℝ) + 1 := centralPath_norm_sq 𝓢 hμ ⟨hC, hT⟩
    unfold IrnSetup.r
    rw [← Real.sqrt_sq (norm_nonneg u), h1]
  have h_tildeT_μ : tildeT 𝓢 μ u = 0 := by
    unfold tildeT
    rw [hT]
    simp [proj]
  have h_transfer := tildeT_transfer 𝓢 μ σ hμ hσ hS hC
  rw [h_tildeT_μ, zero_sub] at h_transfer
  rw [h_transfer, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by nlinarith : (0 : ℝ) ≤ (1 - σ) * μ)]
  have hR : μ * R 𝓢 u = ‖𝓢.Q u‖ := mu_R_eq_Q_norm 𝓢 hμ
  unfold R at hR
  rw [show (1 - σ) * μ * ‖𝓢.φ u + u‖ = (1 - σ) * (μ * ‖𝓢.φ u + u‖) from by ring, hR]
  have hμ_ne : μ ≠ 0 := ne_of_gt hμ
  have hσ_ne : σ ≠ 0 := ne_of_gt hσ
  field_simp

/-! ## §6.3 Hessian-norm proximity. -/

/-- Eq. (6.7). The Hessian-norm proximity
`δ(u, μ) = ‖tildeT_μ(u)‖_{W(u)⁻¹} / μ`. -/
noncomputable def delta (μ : ℝ) (u : H) : ℝ :=
  𝓢.normWinv u (tildeT 𝓢 μ u) / μ

/-- **Lemma 13 (Bounded transfer constant).** For every
`u ∈ Sr ∩ int C`, `‖φ(u) + u‖_{W(u)⁻¹} ≤ 2 √(ν+1)`. -/
theorem transfer_bound {u : H}
    (hS : u ∈ sphere 𝓢) (hC : u ∈ 𝓢.C) :
    𝓢.normWinv u (𝓢.φ u + u) ≤ 2 * Real.sqrt ((𝓢.ν : ℝ) + 1) := by
  have h_tri : 𝓢.normWinv u (𝓢.φ u + u) ≤ 𝓢.normWinv u (𝓢.φ u) + 𝓢.normWinv u u :=
    𝓢.normWinv_triangle u (𝓢.φ u) u
  have h_phi : 𝓢.normWinv u (𝓢.φ u) ≤ Real.sqrt ((𝓢.ν : ℝ) + 1) :=
    𝓢.normWinv_phi_bound u hC
  have h_u : 𝓢.normWinv u u ≤ ‖u‖ := 𝓢.normWinv_le_norm u u
  have h_u_eq : ‖u‖ = Real.sqrt ((𝓢.ν : ℝ) + 1) := by
    have h_norm : ‖u‖ = 𝓢.r := hS
    unfold IrnSetup.r at h_norm
    exact h_norm
  calc 𝓢.normWinv u (𝓢.φ u + u)
      ≤ 𝓢.normWinv u (𝓢.φ u) + 𝓢.normWinv u u := h_tri
    _ ≤ Real.sqrt ((𝓢.ν : ℝ) + 1) + ‖u‖ := by linarith
    _ = Real.sqrt ((𝓢.ν : ℝ) + 1) + Real.sqrt ((𝓢.ν : ℝ) + 1) := by rw [h_u_eq]
    _ = 2 * Real.sqrt ((𝓢.ν : ℝ) + 1) := by ring

/-- **Lemma 14 (Proximity transfer).** Eq. (6.9):
`δ(u, σμ) ≤ δ(u, μ)/σ + 2(1-σ)√(ν+1)/σ` on `Sr ∩ int C`. -/
theorem proximity_transfer
    {μ : ℝ} (hμ : 0 < μ) {σ : ℝ} (hσ : 0 < σ) (hσ' : σ ≤ 1)
    {u : H} (hS : u ∈ sphere 𝓢) (hC : u ∈ 𝓢.C) :
    delta 𝓢 (σ * μ) u ≤
      delta 𝓢 μ u / σ +
        2 * (1 - σ) * Real.sqrt ((𝓢.ν : ℝ) + 1) / σ := by
  unfold delta
  rw [tildeT_transfer 𝓢 μ σ hμ hσ hS hC]
  -- Triangle inequality for `normWinv` applied to `tildeT μ u - (1-σ)μ • (φ u + u)`.
  have h_1sub_μ_nn : 0 ≤ (1 - σ) * μ := mul_nonneg (by linarith) hμ.le
  have h_step1 : 𝓢.normWinv u (tildeT 𝓢 μ u - ((1 - σ) * μ) • (𝓢.φ u + u)) ≤
      𝓢.normWinv u (tildeT 𝓢 μ u) + (1 - σ) * μ * 𝓢.normWinv u (𝓢.φ u + u) := by
    rw [sub_eq_add_neg, ← neg_smul]
    have h_tri := 𝓢.normWinv_triangle u (tildeT 𝓢 μ u) ((-((1 - σ) * μ)) • (𝓢.φ u + u))
    rw [𝓢.normWinv_smul, abs_neg, abs_of_nonneg h_1sub_μ_nn] at h_tri
    exact h_tri
  -- Plug in transfer_bound.
  have h_tb := transfer_bound 𝓢 hS hC
  have h_step2 : 𝓢.normWinv u (tildeT 𝓢 μ u - ((1 - σ) * μ) • (𝓢.φ u + u)) ≤
      𝓢.normWinv u (tildeT 𝓢 μ u) + (1 - σ) * μ * (2 * Real.sqrt ((𝓢.ν : ℝ) + 1)) := by
    have := mul_le_mul_of_nonneg_left h_tb h_1sub_μ_nn
    linarith
  -- Divide by `σμ` and clean up.
  have hσμ_pos : 0 < σ * μ := mul_pos hσ hμ
  have h_div :=
    (div_le_div_iff_of_pos_right hσμ_pos).mpr h_step2
  -- Now match the goal RHS by `field_simp; ring`.
  have hμ_ne : μ ≠ 0 := ne_of_gt hμ
  have hσ_ne : σ ≠ 0 := ne_of_gt hσ
  have h_rhs_eq :
      (𝓢.normWinv u (tildeT 𝓢 μ u) +
            (1 - σ) * μ * (2 * Real.sqrt ((𝓢.ν : ℝ) + 1))) / (σ * μ) =
        𝓢.normWinv u (tildeT 𝓢 μ u) / μ / σ +
          2 * (1 - σ) * Real.sqrt ((𝓢.ν : ℝ) + 1) / σ := by
    field_simp
  linarith

/-- The outer-loop arithmetic underlying Theorem 16: with
`σ = 1 - α / √(ν+1)`, `σ^k ≤ ε` whenever
`k ≥ √(ν+1) / α · log(1/ε)`. Proof via `1 - x ≤ exp(-x)`. -/
theorem outer_iteration_count
    {α : ℝ} (hα_pos : 0 < α) (hα_lt_1 : α < 1)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1)
    {k : ℕ}
    (hk : (k : ℝ) ≥ Real.sqrt ((𝓢.ν : ℝ) + 1) / α * Real.log (1 / ε)) :
    (1 - α / Real.sqrt ((𝓢.ν : ℝ) + 1)) ^ k ≤ ε := by
  set s := Real.sqrt ((𝓢.ν : ℝ) + 1) with hs_def
  have hs_pos : 0 < s := 𝓢.r_pos
  have hs_ge_1 : 1 ≤ s := by
    have hν : 1 ≤ (𝓢.ν : ℝ) := by exact_mod_cast 𝓢.ν_pos
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt ((𝓢.ν : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
  have hα_lt_s : α < s := lt_of_lt_of_le hα_lt_1 hs_ge_1
  have hα_div_pos : 0 < α / s := div_pos hα_pos hs_pos
  have h_one_sub_nn : 0 ≤ 1 - α / s := by
    have : α / s < 1 := (div_lt_one hs_pos).mpr hα_lt_s
    linarith
  have h_1mx_le_exp : 1 - α / s ≤ Real.exp (-(α / s)) := by
    have := Real.add_one_le_exp (-(α / s))
    linarith
  have h_log_1div_eq : Real.log (1 / ε) = -Real.log ε := by
    rw [one_div, Real.log_inv]
  have h_mul : Real.log (1 / ε) ≤ (k : ℝ) * (α / s) := by
    have heq : Real.log (1 / ε) = (s / α * Real.log (1 / ε)) * (α / s) := by
      field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_right hk hα_div_pos.le
  have h_target_ineq : -((k : ℝ) * (α / s)) ≤ Real.log ε := by linarith
  have h_exp_target : Real.exp (-((k : ℝ) * (α / s))) ≤ ε := by
    have := Real.exp_le_exp.mpr h_target_ineq
    rwa [Real.exp_log hε] at this
  calc (1 - α / s) ^ k
      ≤ Real.exp (-(α / s)) ^ k := by gcongr
    _ = Real.exp (-((k : ℝ) * (α / s))) := by
        rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ ε := h_exp_target

/-- The Newton corrector preserves the constraint set. This combines
the conclusions of Proposition 11 (well-definedness within a basin)
and Theorem 12 (the iterates stay on `Sr ∩ int C`). Recorded as a
theorem with a `sorry` proof since the analytic content is not yet
formalised, but the statement is meaningful (the `rjnStep` field is
now linked to Theorem 8 via `resolvent_closed_form`). -/
theorem rjnStep_invariant
    {μ : ℝ} (_hμ : 0 < μ) {u : H} (_hS : u ∈ sphere 𝓢) (_hC : u ∈ 𝓢.C) :
    𝓢.rjnStep μ u ∈ sphere 𝓢 ∧ 𝓢.rjnStep μ u ∈ 𝓢.C := sorry

/-- The Newton corrector contracts the Hessian-norm proximity `δ`
quadratically on a basin of constant radius `ρ*`. This is Lemma 15
(Newton–Kantorovich for the corrector in the self-concordant
`W`-metric); recorded here with `sorry` proof but a meaningful
statement now that `rjnStep` is a field linked to Theorem 8. -/
theorem rjnStep_quadratic_contraction :
    ∃ ρ_star K_star : ℝ, 0 < ρ_star ∧ ρ_star < 1 ∧ 1 ≤ K_star ∧
      ∀ {μ : ℝ}, 0 < μ → ∀ {u : H}, u ∈ sphere 𝓢 → u ∈ 𝓢.C →
        delta 𝓢 μ u ≤ ρ_star →
          delta 𝓢 μ (𝓢.rjnStep μ u) ≤ K_star * (delta 𝓢 μ u) ^ 2 := sorry

/-- **Lemma 15 (Hessian-norm quadratic contraction).** There exist
absolute constants `ρ* ∈ (0,1)` and `K* ≥ 1` such that one Riemannian
Josephy–Newton step contracts the Hessian-norm proximity as
`δ(u⁺, μ) ≤ K* · δ(u, μ)²` whenever `δ(u, μ) ≤ ρ*`. -/
theorem hessian_quadratic_contraction :
    ∃ ρ_star : ℝ, ∃ K_star : ℝ,
      0 < ρ_star ∧ ρ_star < 1 ∧ 1 ≤ K_star ∧
      ∀ {μ : ℝ}, 0 < μ →
        ∀ {u : H}, u ∈ sphere 𝓢 → u ∈ 𝓢.C →
          delta 𝓢 μ u ≤ ρ_star →
            ∀ {u_next : H} {lam : ℝ}, IsRJNStepA 𝓢 μ u u_next lam →
              delta 𝓢 μ u_next ≤ K_star * (delta 𝓢 μ u) ^ 2 := by
  obtain ⟨ρ, K, hρ_pos, hρ_lt, hK_ge, h_contract⟩ := rjnStep_quadratic_contraction 𝓢
  refine ⟨ρ, K, hρ_pos, hρ_lt, hK_ge, ?_⟩
  intros μ hμ u hS hC h_δ u_next _lam h_step
  obtain ⟨h_eq_step, _⟩ := h_step
  rw [h_eq_step]
  exact h_contract hμ hS hC h_δ

/-- **Theorem 16 (Polynomial complexity).** With Hessian-norm
proximity, the path-following scheme
`μ_{k+1} = σ μ_k`, `σ = 1 - α/√(ν+1)`,
followed by `N` corrector steps, maintains `δ(u_k, μ_k) ≤ β`
throughout, with `α, β, N` absolute constants. To reach
`μ_k ≤ ε μ₀` requires at most
`⌈ √(ν+1) / α · log(1/ε) ⌉` outer iterations. -/
theorem polynomial_complexity :
    ∃ α : ℝ, ∃ β : ℝ, ∃ N : ℕ,
      0 < α ∧ α < 1 ∧ 0 < β ∧ β < 1 ∧
      ∀ {μ₀ : ℝ}, 0 < μ₀ →
        ∀ {u₀ : H}, u₀ ∈ sphere 𝓢 → u₀ ∈ 𝓢.C →
          delta 𝓢 μ₀ u₀ ≤ β →
            let σ := 1 - α / Real.sqrt ((𝓢.ν : ℝ) + 1)
            ∃ seq : ℕ → H, seq 0 = u₀ ∧
              ∀ k, seq k ∈ sphere 𝓢 ∩ 𝓢.C ∧
                   delta 𝓢 (σ ^ k * μ₀) (seq k) ≤ β ∧
              ∀ ε : ℝ, 0 < ε →
                ∀ k, k ≥ ⌈Real.sqrt ((𝓢.ν : ℝ) + 1) / α
                          * Real.log (1 / ε)⌉₊ →
                  σ ^ k * μ₀ ≤ ε * μ₀ := sorry

end Irn
