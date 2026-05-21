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

namespace IrnSetup

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

variable (𝓢 : IrnSetup X Y)

/-- The tangentially-projected residual `tildeT_μ(u) = P_u T_μ(u)`. -/
noncomputable def tildeT (μ : ℝ) (u : H X Y) : H X Y :=
  proj u (𝓢.T μ u)

/-! ## §6.1 Proximity transfer identity. -/

/-- **Eq. (6.1).** On `Sr ∩ int C`, the projector simplifies to
`P_u φ(u) = φ(u) + u`. -/
theorem proj_phi_on_sphere {u : H X Y}
    (hS : u ∈ 𝓢.sphere) (hC : u ∈ 𝓢.C_interior) :
    proj u (𝓢.φ u) = 𝓢.φ u + u := by
  unfold proj
  rw [𝓢.inner_u_phi u hC]
  have huu : ‖u‖ ^ 2 = (𝓢.ν : ℝ) + 1 := by
    have hnorm : ‖u‖ = 𝓢.r := hS
    rw [hnorm, 𝓢.r_sq]
  rw [huu]
  have hpos : (0 : ℝ) < (𝓢.ν : ℝ) + 1 := by positivity
  rw [neg_div, div_self (ne_of_gt hpos), neg_smul, one_smul, sub_neg_eq_add]

/-- **Eq. (6.3).** Affine-in-`μ` proximity transfer identity. -/
theorem tildeT_transfer (μ σ : ℝ) (hμ : 0 < μ) (hσ : 0 < σ) {u : H X Y}
    (hS : u ∈ 𝓢.sphere) (hC : u ∈ 𝓢.C_interior) :
    𝓢.tildeT (σ * μ) u = 𝓢.tildeT μ u - ((1 - σ) * μ) • (𝓢.φ u + u) := by
  unfold tildeT
  rw [proj_of_orthogonal u _ (𝓢.tangent_T (mul_pos hσ hμ) hS hC),
      proj_of_orthogonal u _ (𝓢.tangent_T hμ hS hC)]
  unfold T
  module

/-! ## §6.2 Failure of Euclidean tolerances. -/

/-- The Euclidean transfer constant `R(u) = ‖φ(u) + u‖`. -/
noncomputable def R (u : H X Y) : ℝ := ‖𝓢.φ u + u‖

/-- The identity `μ R(u*(μ)) = ‖Q(u*(μ))‖`. -/
theorem mu_R_eq_Q_norm {μ : ℝ} (hμ : 0 < μ) :
    μ * 𝓢.R (𝓢.centralPathPoint μ hμ) =
      ‖𝓢.Q (𝓢.centralPathPoint μ hμ)‖ := by
  set u := 𝓢.centralPathPoint μ hμ
  obtain ⟨_, hT⟩ := 𝓢.centralPathPoint_isCentralPathPoint μ hμ
  unfold T at hT
  unfold R
  have hT' : 𝓢.Q u + (μ • u + μ • 𝓢.φ u) = 0 := by
    rw [← add_assoc]; exact hT
  have hQ : 𝓢.Q u = -(μ • (𝓢.φ u + u)) := by
    have h1 : 𝓢.Q u = -(μ • u + μ • 𝓢.φ u) := add_eq_zero_iff_eq_neg.mp hT'
    rw [h1, smul_add, add_comm (μ • 𝓢.φ u)]
  rw [hQ, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hμ]

/-- **Proposition 12 (Failure of Euclidean tolerances).** -/
theorem euclidean_failure
    {μ : ℝ} (hμ : 0 < μ) {σ : ℝ} (hσ : 0 < σ) (hσ' : σ ≤ 1) :
    ‖𝓢.tildeT (σ * μ) (𝓢.centralPathPoint μ hμ)‖ / (σ * μ) =
      ((1 - σ) / σ) * (‖𝓢.Q (𝓢.centralPathPoint μ hμ)‖ / μ) := by
  set u := 𝓢.centralPathPoint μ hμ
  obtain ⟨hC, hT⟩ := 𝓢.centralPathPoint_isCentralPathPoint μ hμ
  have hS : u ∈ 𝓢.sphere := by
    show ‖u‖ = 𝓢.r
    have h1 : ‖u‖ ^ 2 = (𝓢.ν : ℝ) + 1 :=
      𝓢.centralPath_norm_sq hμ ⟨hC, hT⟩
    unfold r
    rw [← Real.sqrt_sq (norm_nonneg u), h1]
  have h_tildeT_μ : 𝓢.tildeT μ u = 0 := by
    unfold tildeT
    rw [hT]
    simp [proj]
  have h_transfer := 𝓢.tildeT_transfer μ σ hμ hσ hS hC
  rw [h_tildeT_μ, zero_sub] at h_transfer
  rw [h_transfer, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by nlinarith : (0 : ℝ) ≤ (1 - σ) * μ)]
  have hR : μ * 𝓢.R u = ‖𝓢.Q u‖ := 𝓢.mu_R_eq_Q_norm hμ
  unfold R at hR
  rw [show (1 - σ) * μ * ‖𝓢.φ u + u‖ = (1 - σ) * (μ * ‖𝓢.φ u + u‖)
        from by ring, hR]
  have hμ_ne : μ ≠ 0 := ne_of_gt hμ
  have hσ_ne : σ ≠ 0 := ne_of_gt hσ
  field_simp

/-! ## §6.3 Hessian-norm proximity. -/

/-- Eq. (6.7). The Hessian-norm proximity
`δ(u, μ) = ‖tildeT_μ(u)‖_{W(u)⁻¹} / μ`. -/
noncomputable def delta (μ : ℝ) (u : H X Y) : ℝ :=
  𝓢.normWinv u (𝓢.tildeT μ u) / μ

/-- **Lemma 13 (Bounded transfer constant).** -/
theorem transfer_bound {u : H X Y}
    (hS : u ∈ 𝓢.sphere) (hC : u ∈ 𝓢.C_interior) :
    𝓢.normWinv u (𝓢.φ u + u) ≤ 2 * Real.sqrt ((𝓢.ν : ℝ) + 1) := by
  have h_tri : 𝓢.normWinv u (𝓢.φ u + u) ≤
      𝓢.normWinv u (𝓢.φ u) + 𝓢.normWinv u u :=
    𝓢.normWinv_triangle u hC (𝓢.φ u) u
  have h_phi : 𝓢.normWinv u (𝓢.φ u) ≤ Real.sqrt ((𝓢.ν : ℝ) + 1) :=
    𝓢.normWinv_phi_bound u hC
  have h_u : 𝓢.normWinv u u ≤ ‖u‖ := 𝓢.normWinv_le_norm u hC u
  have h_u_eq : ‖u‖ = Real.sqrt ((𝓢.ν : ℝ) + 1) := by
    have h_norm : ‖u‖ = 𝓢.r := hS
    unfold r at h_norm
    exact h_norm
  calc 𝓢.normWinv u (𝓢.φ u + u)
      ≤ 𝓢.normWinv u (𝓢.φ u) + 𝓢.normWinv u u := h_tri
    _ ≤ Real.sqrt ((𝓢.ν : ℝ) + 1) + ‖u‖ := by linarith
    _ = Real.sqrt ((𝓢.ν : ℝ) + 1) + Real.sqrt ((𝓢.ν : ℝ) + 1) := by rw [h_u_eq]
    _ = 2 * Real.sqrt ((𝓢.ν : ℝ) + 1) := by ring

/-- **Lemma 14 (Proximity transfer).** -/
theorem proximity_transfer
    {μ : ℝ} (hμ : 0 < μ) {σ : ℝ} (hσ : 0 < σ) (hσ' : σ ≤ 1)
    {u : H X Y} (hS : u ∈ 𝓢.sphere) (hC : u ∈ 𝓢.C_interior) :
    𝓢.delta (σ * μ) u ≤
      𝓢.delta μ u / σ +
        2 * (1 - σ) * Real.sqrt ((𝓢.ν : ℝ) + 1) / σ := by
  unfold delta
  rw [𝓢.tildeT_transfer μ σ hμ hσ hS hC]
  have h_1sub_μ_nn : 0 ≤ (1 - σ) * μ := mul_nonneg (by linarith) hμ.le
  have h_step1 :
      𝓢.normWinv u (𝓢.tildeT μ u - ((1 - σ) * μ) • (𝓢.φ u + u)) ≤
      𝓢.normWinv u (𝓢.tildeT μ u) +
        (1 - σ) * μ * 𝓢.normWinv u (𝓢.φ u + u) := by
    rw [sub_eq_add_neg, ← neg_smul]
    have h_tri := 𝓢.normWinv_triangle u hC (𝓢.tildeT μ u)
      ((-((1 - σ) * μ)) • (𝓢.φ u + u))
    rw [𝓢.normWinv_smul, abs_neg, abs_of_nonneg h_1sub_μ_nn] at h_tri
    exact h_tri
  have h_tb := 𝓢.transfer_bound hS hC
  have h_step2 :
      𝓢.normWinv u (𝓢.tildeT μ u - ((1 - σ) * μ) • (𝓢.φ u + u)) ≤
      𝓢.normWinv u (𝓢.tildeT μ u) +
        (1 - σ) * μ * (2 * Real.sqrt ((𝓢.ν : ℝ) + 1)) := by
    have := mul_le_mul_of_nonneg_left h_tb h_1sub_μ_nn
    linarith
  have hσμ_pos : 0 < σ * μ := mul_pos hσ hμ
  have h_div :=
    (div_le_div_iff_of_pos_right hσμ_pos).mpr h_step2
  have hμ_ne : μ ≠ 0 := ne_of_gt hμ
  have hσ_ne : σ ≠ 0 := ne_of_gt hσ
  have h_rhs_eq :
      (𝓢.normWinv u (𝓢.tildeT μ u) +
            (1 - σ) * μ * (2 * Real.sqrt ((𝓢.ν : ℝ) + 1))) / (σ * μ) =
        𝓢.normWinv u (𝓢.tildeT μ u) / μ / σ +
          2 * (1 - σ) * Real.sqrt ((𝓢.ν : ℝ) + 1) / σ := by
    field_simp
  linarith

/-- The outer-loop arithmetic underlying Theorem 16. -/
theorem outer_iteration_count
    {α : ℝ} (hα_pos : 0 < α) (hα_lt_1 : α < 1)
    {ε : ℝ} (hε : 0 < ε)
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

/-- The Newton corrector contracts the Hessian-norm proximity `δ`
quadratically on a basin of constant radius `ρ*`. -/
theorem rjnStep_quadratic_contraction :
    ∃ ρ_star K_star : ℝ, 0 < ρ_star ∧ ρ_star < 1 ∧ 1 ≤ K_star ∧
      ∀ {μ : ℝ}, 0 < μ → ∀ {u : H X Y}, u ∈ 𝓢.sphere → u ∈ 𝓢.C_interior →
        𝓢.delta μ u ≤ ρ_star →
          𝓢.delta μ (𝓢.rjnStep μ u) ≤ K_star * (𝓢.delta μ u) ^ 2 := by
  obtain ⟨ρ_star, K_star, hρ_pos, hρ_lt, hK_ge, h_field⟩ :=
    𝓢.rjnStep_delta_contraction
  refine ⟨ρ_star, K_star, hρ_pos, hρ_lt, hK_ge, ?_⟩
  intros μ hμ u hS hC h_δ
  have h_norm_sq : ‖u‖ ^ 2 = (𝓢.ν : ℝ) + 1 := by
    have hn : ‖u‖ = 𝓢.r := hS
    rw [hn, 𝓢.r_sq]
  have h_inv := 𝓢.rjnStep_invariant hμ hS hC
  have h_delta_u : 𝓢.delta μ u =
      𝓢.normWinv u (𝓢.Q u + μ • u + μ • 𝓢.φ u) / μ := by
    unfold delta tildeT
    rw [proj_of_orthogonal u _ (𝓢.tangent_T hμ hS hC)]
    rfl
  have h_delta_step : 𝓢.delta μ (𝓢.rjnStep μ u) =
      𝓢.normWinv (𝓢.rjnStep μ u)
        (𝓢.Q (𝓢.rjnStep μ u) + μ • (𝓢.rjnStep μ u) +
            μ • 𝓢.φ (𝓢.rjnStep μ u)) / μ := by
    unfold delta tildeT
    rw [proj_of_orthogonal _ _ (𝓢.tangent_T hμ h_inv.1 h_inv.2)]
    rfl
  rw [h_delta_step, h_delta_u]
  rw [h_delta_u] at h_δ
  exact h_field μ hμ u h_norm_sq hC h_δ

/-- **Lemma 15 (Hessian-norm quadratic contraction).** -/
theorem hessian_quadratic_contraction :
    ∃ ρ_star : ℝ, ∃ K_star : ℝ,
      0 < ρ_star ∧ ρ_star < 1 ∧ 1 ≤ K_star ∧
      ∀ {μ : ℝ}, 0 < μ →
        ∀ {u : H X Y}, u ∈ 𝓢.sphere → u ∈ 𝓢.C_interior →
          𝓢.delta μ u ≤ ρ_star →
            ∀ {u_next : H X Y} {lam : ℝ}, IsRJNStepA 𝓢 μ u u_next lam →
              𝓢.delta μ u_next ≤ K_star * (𝓢.delta μ u) ^ 2 := by
  obtain ⟨ρ, K, hρ_pos, hρ_lt, hK_ge, h_contract⟩ :=
    𝓢.rjnStep_quadratic_contraction
  refine ⟨ρ, K, hρ_pos, hρ_lt, hK_ge, ?_⟩
  intros μ hμ u hS hC h_δ u_next _lam h_step
  obtain ⟨h_eq_step, _⟩ := h_step
  rw [h_eq_step]
  exact h_contract hμ hS hC h_δ

/-- **Theorem 16 (Polynomial complexity).** -/
theorem polynomial_complexity :
    ∃ α : ℝ, ∃ β : ℝ, ∃ N : ℕ,
      0 < α ∧ α < 1 ∧ 0 < β ∧ β < 1 ∧
      ∀ {μ₀ : ℝ}, 0 < μ₀ →
        ∀ {u₀ : H X Y}, u₀ ∈ 𝓢.sphere → u₀ ∈ 𝓢.C_interior →
          𝓢.delta μ₀ u₀ ≤ β →
            let σ := 1 - α / Real.sqrt ((𝓢.ν : ℝ) + 1)
            ∃ seq : ℕ → H X Y, seq 0 = u₀ ∧
              ∀ k, seq k ∈ 𝓢.sphere ∩ 𝓢.C_interior ∧
                   𝓢.delta (σ ^ k * μ₀) (seq k) ≤ β ∧
              ∀ ε : ℝ, 0 < ε →
                ∀ k, k ≥ ⌈Real.sqrt ((𝓢.ν : ℝ) + 1) / α
                          * Real.log (1 / ε)⌉₊ →
                  σ ^ k * μ₀ ≤ ε * μ₀ := by
  obtain ⟨ρ_star, K_star, h_ρ_pos, h_ρ_lt, h_K_ge, h_contract⟩ :=
    𝓢.rjnStep_quadratic_contraction
  set α : ℝ := ρ_star / (36 * (K_star + 1)) with hα_def
  have h_K_pos : (0 : ℝ) < K_star + 1 := by linarith
  have h_denom_pos : (0 : ℝ) < 36 * (K_star + 1) := by linarith
  have hα_pos : 0 < α := by rw [hα_def]; positivity
  have h_36K1_α : 36 * (K_star + 1) * α = ρ_star := by
    rw [hα_def]; field_simp
  have hα_le : α ≤ 1 / 72 := by
    rw [hα_def, div_le_div_iff₀ h_denom_pos (by norm_num : (0 : ℝ) < 72)]
    nlinarith [h_ρ_lt, h_K_ge]
  have hα_lt_1 : α < 1 := by linarith
  refine ⟨α, α, 1, hα_pos, hα_lt_1, hα_pos, hα_lt_1, ?_⟩
  set s : ℝ := Real.sqrt ((𝓢.ν : ℝ) + 1) with hs_def
  have hs_pos : 0 < s := 𝓢.r_pos
  have hs_ge_1 : 1 ≤ s := by
    have hν : 1 ≤ (𝓢.ν : ℝ) := by exact_mod_cast 𝓢.ν_pos
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ s := Real.sqrt_le_sqrt (by linarith)
  have hα_div_pos : 0 < α / s := div_pos hα_pos hs_pos
  have hα_div_le_α : α / s ≤ α := by
    rw [div_le_iff₀ hs_pos]
    nlinarith [hα_pos, hs_ge_1]
  have hα_div_lt_1 : α / s < 1 := lt_of_le_of_lt hα_div_le_α hα_lt_1
  intros μ₀ hμ₀ u₀ hS hC h_δ_u₀ σ
  have hσ_pos : 0 < σ := by show 0 < 1 - α / s; linarith
  have hσ_le_1 : σ ≤ 1 := by show 1 - α / s ≤ 1; linarith
  have hσ_ge_half : 1/2 ≤ σ := by
    show 1/2 ≤ 1 - α / s
    have : α / s ≤ 1/72 := le_trans hα_div_le_α hα_le
    linarith
  have h_one_sub_σ : 1 - σ = α / s := by show 1 - (1 - α / s) = α / s; ring
  let seq_fn : ℕ → H X Y := fun k =>
    Nat.rec (motive := fun _ => H X Y) u₀
      (fun n seq_n => 𝓢.rjnStep (σ^(n+1) * μ₀) seq_n) k
  have h_seq_0 : seq_fn 0 = u₀ := rfl
  have h_seq_succ : ∀ k, seq_fn (k+1) = 𝓢.rjnStep (σ^(k+1) * μ₀) (seq_fn k) :=
    fun _ => rfl
  have h_inv : ∀ k, seq_fn k ∈ 𝓢.sphere ∩ 𝓢.C_interior ∧
                    𝓢.delta (σ^k * μ₀) (seq_fn k) ≤ α := by
    intro k
    induction k with
    | zero =>
      refine ⟨⟨hS, hC⟩, ?_⟩
      show 𝓢.delta (σ^0 * μ₀) u₀ ≤ α
      simp
      exact h_δ_u₀
    | succ k ih =>
      obtain ⟨h_sC_k, h_δ_k⟩ := ih
      have h_S_k : seq_fn k ∈ 𝓢.sphere := h_sC_k.1
      have h_C_k : seq_fn k ∈ 𝓢.C_interior := h_sC_k.2
      have hμ_k_pos : 0 < σ^k * μ₀ := by positivity
      have hμ_succ_pos : 0 < σ^(k+1) * μ₀ := by positivity
      have h_pt := 𝓢.proximity_transfer hμ_k_pos hσ_pos hσ_le_1 h_S_k h_C_k
      have h_pow_succ_eq : σ * (σ^k * μ₀) = σ^(k+1) * μ₀ := by ring
      rw [h_pow_succ_eq] at h_pt
      have h_pre_contract : 𝓢.delta (σ^(k+1) * μ₀) (seq_fn k) ≤ 6 * α := by
        have h_step : 𝓢.delta (σ^(k+1) * μ₀) (seq_fn k) ≤ 3 * α / σ := by
          calc 𝓢.delta (σ^(k+1) * μ₀) (seq_fn k)
              ≤ 𝓢.delta (σ^k * μ₀) (seq_fn k) / σ +
                  2 * (1 - σ) * s / σ := h_pt
            _ ≤ α / σ + 2 * (α / s) * s / σ := by
                apply add_le_add
                · exact div_le_div_of_nonneg_right h_δ_k hσ_pos.le
                · rw [h_one_sub_σ]
            _ = 3 * α / σ := by field_simp; ring
        calc 𝓢.delta (σ^(k+1) * μ₀) (seq_fn k) ≤ 3 * α / σ := h_step
          _ ≤ 6 * α := by
              have h_2σ_ge_1 : 2 * σ ≥ 1 := by linarith [hσ_ge_half]
              have h_prod : 3 * α ≤ 6 * α * σ := by nlinarith [hα_pos, h_2σ_ge_1]
              exact (div_le_iff₀ hσ_pos).mpr h_prod
      have h_6α_le_ρ : 6 * α ≤ ρ_star := by
        have h_36K1_ge_6 : (36 : ℝ) * (K_star + 1) ≥ 6 := by linarith
        nlinarith [h_36K1_α, hα_pos, h_K_ge]
      have h_in_basin : 𝓢.delta (σ^(k+1) * μ₀) (seq_fn k) ≤ ρ_star :=
        le_trans h_pre_contract h_6α_le_ρ
      have h_invariant := 𝓢.rjnStep_invariant hμ_succ_pos h_S_k h_C_k
      refine ⟨h_invariant, ?_⟩
      rw [h_seq_succ]
      have h_contract' := h_contract hμ_succ_pos h_S_k h_C_k h_in_basin
      have h_delta_nn : 0 ≤ 𝓢.delta (σ^(k+1) * μ₀) (seq_fn k) := by
        unfold delta
        apply div_nonneg
        · exact 𝓢.normWinv_nonneg _ _
        · exact hμ_succ_pos.le
      calc 𝓢.delta (σ^(k+1) * μ₀) (𝓢.rjnStep (σ^(k+1) * μ₀) (seq_fn k))
          ≤ K_star * (𝓢.delta (σ^(k+1) * μ₀) (seq_fn k)) ^ 2 := h_contract'
        _ ≤ K_star * (6 * α) ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ (by linarith : (0 : ℝ) ≤ K_star)
            exact sq_le_sq' (by linarith) h_pre_contract
        _ = 36 * K_star * α ^ 2 := by ring
        _ ≤ α := by
            have h1 : 36 * K_star * α ≤ 36 * (K_star + 1) * α := by
              nlinarith [hα_pos, h_K_ge]
            have h2 : 36 * (K_star + 1) * α ≤ 1 := by
              rw [h_36K1_α]; linarith
            have h3 : 36 * K_star * α ≤ 1 := le_trans h1 h2
            nlinarith [hα_pos]
  refine ⟨seq_fn, rfl, ?_⟩
  intro k
  refine ⟨(h_inv k).1, (h_inv k).2, ?_⟩
  intros ε hε k_iter hk_iter
  have hk_iter_real : (k_iter : ℝ) ≥ s / α * Real.log (1 / ε) := by
    calc (k_iter : ℝ)
        ≥ (⌈s / α * Real.log (1 / ε)⌉₊ : ℝ) := by exact_mod_cast hk_iter
      _ ≥ s / α * Real.log (1 / ε) := Nat.le_ceil _
  have h_oic := 𝓢.outer_iteration_count hα_pos hα_lt_1 hε hk_iter_real
  have h_pow_le : σ^k_iter ≤ ε := h_oic
  exact mul_le_mul_of_nonneg_right h_pow_le hμ₀.le

end IrnSetup

end Irn
