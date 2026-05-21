/-
# Analytic content of the IRN method (stubbed with `sorry`)

The structural data of an IRN setup — the cones, the KKT operator `Q`,
the barrier-gradient `φ`, the embedding map `M`, the bilinear form
`Px_bilinform`, the τ-projection, etc. — are all derivable from a
`IrnSetup` (see `Irn.Setting`). This file declares the
remaining ingredients (the `W(u)⁻¹` dual norm, the Hessian
preconditioner, the Riemannian Josephy–Newton corrector and Lagrange
multiplier, Minty's resolvent existence, and the two
Newton–Kantorovich basins) as `sorry`-stubbed `def`s / `theorem`s in
the `IrnSetup` namespace, so that the `toIrnSetup` bridge in
`Irn.Bridge` only needs a `IrnSetup` as input (no separate analytic
hypothesis bundle).

Each `sorry` below corresponds to a paper-level claim that is either:

* part of standard LHSCB / monotone-operator / Newton–Kantorovich
  theory (resolvent existence, Hessian-norm contraction, Euclidean
  basin), or
* a fact about the IRN dual norm `‖·‖_{W(u)⁻¹}` (which is built from
  `W = I + ∇²F*`, requiring Hessian machinery we do not yet formalise).

Filling these in is the substantive future work of the formalisation;
the structural derivations (eg. `inner_u_M`, `Px_quad_form_psd`,
`inner_u_Q`) are already proven `sorry`-free.

Paper references:
* §3.2 (a posteriori error bound) — `normWinv_phi_bound`
* §5.2, eq. (5.3) — `rjnStep`, `rjnLambda`
* §5.4, Proposition 11 — `rjnLambda_at_central`,
  `rjnLambda_continuousAt_central`
* §5.5, Theorem 12 — `rjnStep_euclidean_basin`
* §6.3, Lemma 15 — `rjnStep_delta_contraction`
* Appendix — `resolvent_exists` (Minty's theorem for `H_k + Ψ`)
-/

import Irn.Setting

namespace Irn
namespace IrnSetup

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  (𝓢 : IrnSetup X Y)

/-! ### Hessian bilinear form -/

/-- The Hessian bilinear form of `F_lhscb` (≡ paper's `F^*` in
derivative-relevant quantities; see `Setting.lean` docstring on
`f_lhscb`) at `u`, evaluated at `(v, w)`. Captures `∇²F^*(u)(v, w)`. -/
noncomputable def hessianBilin (u : H X Y) (v w : H X Y) : ℝ :=
  iteratedFDerivWithin ℝ 2 𝓢.F_lhscb.f
    (interior (𝓢.K_f_lifted ∩ 𝓢.K_g_lifted)) u ![v, w]

/-- The Hessian bilinear form is PSD: `0 ≤ ∇²F^*(u)(v, v)`.
Inherited from `LHSCB.self_concordant_hessian_nonneg`. -/
theorem hessianBilin_self_nonneg (u : H X Y) (hu : u ∈ 𝓢.C_interior)
    (v : H X Y) : 0 ≤ 𝓢.hessianBilin u v v := by
  have hu' : u ∈ interior (𝓢.K_f_lifted ∩ 𝓢.K_g_lifted) :=
    𝓢.C_interior_subset_F_interior hu
  have := 𝓢.F_lhscb.self_concordant_hessian_nonneg u hu' v
  show 0 ≤ iteratedFDerivWithin ℝ 2 𝓢.F_lhscb.f
    (interior (𝓢.K_f_lifted ∩ 𝓢.K_g_lifted)) u ![v, v]
  convert this using 2
  funext i
  fin_cases i <;> rfl

/-- **Hessian-times-self identity** for `hessianBilin`. On `C_interior`,
`hessianBilin u u h = -⟨h, φ u⟩`. Derived from
`LHSCB.hessian_fderiv_apply_self_inner` for `F_lhscb` by translating
through `iteratedFDeriv_two_apply` (on the open `interior`). -/
theorem hessianBilin_apply_self (u : H X Y) (hu : u ∈ 𝓢.C_interior)
    (h : H X Y) : 𝓢.hessianBilin u u h = -inner ℝ h (𝓢.φ u) := by
  have hu' : u ∈ interior (𝓢.K_f_lifted ∩ 𝓢.K_g_lifted) :=
    𝓢.C_interior_subset_F_interior hu
  show iteratedFDerivWithin ℝ 2 𝓢.F_lhscb.f
    (interior (𝓢.K_f_lifted ∩ 𝓢.K_g_lifted)) u ![u, h] = -inner ℝ h (𝓢.φ u)
  have h_eq : iteratedFDerivWithin ℝ 2 𝓢.F_lhscb.f
        (interior (𝓢.K_f_lifted ∩ 𝓢.K_g_lifted)) u =
      iteratedFDeriv ℝ 2 𝓢.F_lhscb.f u :=
    iteratedFDerivWithin_of_isOpen 2 isOpen_interior hu'
  rw [h_eq, iteratedFDeriv_two_apply]
  show (fderiv ℝ (fderiv ℝ 𝓢.F_lhscb.f) u) u h = -inner ℝ h (𝓢.φ u)
  rw [𝓢.F_lhscb.hessian_fderiv_apply_self_inner u hu' h,
      ← 𝓢.phi_eq_F_grad u hu]

/-- `hessianBilin u u u = ν + 1` on `C_interior`. Follows from
`hessianBilin_apply_self` at `h = u` and the Euler identity
`⟨u, φ u⟩ = -(ν + 1)` (which is `inner_u_phi`). -/
theorem hessianBilin_self_self (u : H X Y) (hu : u ∈ 𝓢.C_interior) :
    𝓢.hessianBilin u u u = (𝓢.ν : ℝ) + 1 := by
  rw [𝓢.hessianBilin_apply_self u hu u, 𝓢.inner_u_phi u hu]
  ring

/-- On `C_interior`, `hessianBilin u v w` agrees with the (curried)
second Fréchet derivative `(fderiv (fderiv F_lhscb.f) u) v w`.
Via `iteratedFDeriv_two_apply` on the open `interior`. -/
theorem hessianBilin_eq_fderiv (u : H X Y) (hu : u ∈ 𝓢.C_interior)
    (v w : H X Y) :
    𝓢.hessianBilin u v w = (fderiv ℝ (fderiv ℝ 𝓢.F_lhscb.f) u) v w := by
  have hu' : u ∈ interior (𝓢.K_f_lifted ∩ 𝓢.K_g_lifted) :=
    𝓢.C_interior_subset_F_interior hu
  show iteratedFDerivWithin ℝ 2 𝓢.F_lhscb.f
    (interior (𝓢.K_f_lifted ∩ 𝓢.K_g_lifted)) u ![v, w] = _
  rw [iteratedFDerivWithin_of_isOpen 2 isOpen_interior hu',
      iteratedFDeriv_two_apply]
  rfl

/-- `hessianBilin u · ·` is bilinear (linear in each slot). -/
theorem hessianBilin_add_left (u : H X Y) (hu : u ∈ 𝓢.C_interior)
    (v₁ v₂ w : H X Y) :
    𝓢.hessianBilin u (v₁ + v₂) w =
      𝓢.hessianBilin u v₁ w + 𝓢.hessianBilin u v₂ w := by
  rw [𝓢.hessianBilin_eq_fderiv u hu, 𝓢.hessianBilin_eq_fderiv u hu,
      𝓢.hessianBilin_eq_fderiv u hu]
  rw [map_add]
  rfl

theorem hessianBilin_smul_left (u : H X Y) (hu : u ∈ 𝓢.C_interior)
    (r : ℝ) (v w : H X Y) :
    𝓢.hessianBilin u (r • v) w = r * 𝓢.hessianBilin u v w := by
  rw [𝓢.hessianBilin_eq_fderiv u hu, 𝓢.hessianBilin_eq_fderiv u hu]
  rw [map_smul]
  rfl

theorem hessianBilin_add_right (u : H X Y) (hu : u ∈ 𝓢.C_interior)
    (v w₁ w₂ : H X Y) :
    𝓢.hessianBilin u v (w₁ + w₂) =
      𝓢.hessianBilin u v w₁ + 𝓢.hessianBilin u v w₂ := by
  rw [𝓢.hessianBilin_eq_fderiv u hu, 𝓢.hessianBilin_eq_fderiv u hu,
      𝓢.hessianBilin_eq_fderiv u hu]
  exact ContinuousLinearMap.map_add _ _ _

theorem hessianBilin_smul_right (u : H X Y) (hu : u ∈ 𝓢.C_interior)
    (r : ℝ) (v w : H X Y) :
    𝓢.hessianBilin u v (r • w) = r * 𝓢.hessianBilin u v w := by
  rw [𝓢.hessianBilin_eq_fderiv u hu, 𝓢.hessianBilin_eq_fderiv u hu]
  exact ContinuousLinearMap.map_smul _ _ _

/-- `hessianBilin u · ·` is symmetric: a consequence of
`second_derivative_symmetric_of_eventually` for `F_lhscb.f`. -/
theorem hessianBilin_symm (u : H X Y) (hu : u ∈ 𝓢.C_interior) (v w : H X Y) :
    𝓢.hessianBilin u v w = 𝓢.hessianBilin u w v := by
  rw [𝓢.hessianBilin_eq_fderiv u hu, 𝓢.hessianBilin_eq_fderiv u hu]
  have hu' : u ∈ interior (𝓢.K_f_lifted ∩ 𝓢.K_g_lifted) :=
    𝓢.C_interior_subset_F_interior hu
  have hf_C3 : ContDiffOn ℝ 3 𝓢.F_lhscb.f
      (interior (𝓢.K_f_lifted ∩ 𝓢.K_g_lifted)) := 𝓢.F_lhscb.contDiff
  have h_ff_diff_eventually : ∀ᶠ y in nhds u,
      HasFDerivAt 𝓢.F_lhscb.f (fderiv ℝ 𝓢.F_lhscb.f y) y := by
    filter_upwards [isOpen_interior.mem_nhds hu'] with y hy
    exact ((hf_C3.differentiableOn (by norm_num)).differentiableAt
      (isOpen_interior.mem_nhds hy)).hasFDerivAt
  have h_fderiv_C2 : ContDiffOn ℝ 2 (fderiv ℝ 𝓢.F_lhscb.f)
      (interior (𝓢.K_f_lifted ∩ 𝓢.K_g_lifted)) := by
    have h1 : ContDiffOn ℝ 2
        (fderivWithin ℝ 𝓢.F_lhscb.f (interior (𝓢.K_f_lifted ∩ 𝓢.K_g_lifted)))
        (interior (𝓢.K_f_lifted ∩ 𝓢.K_g_lifted)) := by
      have := hf_C3.fderivWithin isOpen_interior.uniqueDiffOn (m := 2) (by norm_num)
      simpa using this
    exact h1.congr (fun y hy => (fderivWithin_of_isOpen isOpen_interior hy).symm)
  have h_fderiv_diffAt : DifferentiableAt ℝ (fderiv ℝ 𝓢.F_lhscb.f) u :=
    (h_fderiv_C2.differentiableOn (by norm_num)).differentiableAt
      (isOpen_interior.mem_nhds hu')
  exact second_derivative_symmetric_of_eventually h_ff_diff_eventually
    h_fderiv_diffAt.hasFDerivAt v w

/-- **PSD Cauchy-Schwarz** for `hessianBilin`. On `C_interior`,
`(hessianBilin u v w)² ≤ hessianBilin u v v · hessianBilin u w w`.
Standard discriminant argument: `0 ≤ hessianBilin u (v - λw) (v - λw)` for all
`λ`, hence the quadratic in λ has non-positive discriminant. -/
theorem hessianBilin_CS (u : H X Y) (hu : u ∈ 𝓢.C_interior) (v w : H X Y) :
    (𝓢.hessianBilin u v w) ^ 2 ≤
      𝓢.hessianBilin u v v * 𝓢.hessianBilin u w w := by
  -- Set a := hessianBilin u v v, b := hessianBilin u v w, c := hessianBilin u w w.
  -- Hypothesis: ∀ λ, 0 ≤ a - 2λb + λ²c. We want b² ≤ ac.
  set a := 𝓢.hessianBilin u v v with ha_def
  set b := 𝓢.hessianBilin u v w with hb_def
  set c := 𝓢.hessianBilin u w w with hc_def
  -- Expansion: hessianBilin u (v - λw) (v - λw) = a - 2λb + λ²c.
  have h_expand : ∀ lam : ℝ, 𝓢.hessianBilin u (v - lam • w) (v - lam • w) =
      a - 2 * lam * b + lam^2 * c := by
    intro lam
    have h_sub : v - lam • w = v + (-lam) • w := by rw [neg_smul, sub_eq_add_neg]
    rw [h_sub, 𝓢.hessianBilin_add_left u hu,
        𝓢.hessianBilin_add_right u hu, 𝓢.hessianBilin_add_right u hu,
        𝓢.hessianBilin_smul_right u hu, 𝓢.hessianBilin_smul_right u hu,
        𝓢.hessianBilin_smul_left u hu, 𝓢.hessianBilin_smul_left u hu,
        𝓢.hessianBilin_symm u hu w v]
    ring
  -- For all lam, the quadratic a - 2λb + λ²c ≥ 0.
  have h_quad_nn : ∀ lam : ℝ, 0 ≤ a - 2 * lam * b + lam^2 * c := by
    intro lam
    rw [← h_expand lam]
    exact 𝓢.hessianBilin_self_nonneg u hu _
  -- Case split on c.
  by_cases hc_zero : c = 0
  · -- c = 0: then a - 2λb ≥ 0 for all λ, hence b = 0.
    have h_b_zero : b = 0 := by
      by_contra hb_ne
      -- Pick lam so that 2λb > a.
      rcases lt_or_gt_of_ne hb_ne with hb_neg | hb_pos
      · -- b < 0: pick large positive lam to make 2λb very negative, hence -2λb very positive...
        -- We need a - 2λb < 0. Need 2λb > a. For b < 0, pick lam < 0 large in magnitude.
        have := h_quad_nn ((a + 1) / (2 * b))
        rw [hc_zero] at this
        have h_2b : (2 * b) ≠ 0 := by linarith
        have : a - 2 * ((a + 1) / (2 * b)) * b + ((a + 1) / (2 * b))^2 * 0 ≥ 0 := by linarith
        simp at this
        field_simp at this
        linarith
      · -- b > 0: similar with positive lam.
        have := h_quad_nn ((a + 1) / (2 * b))
        rw [hc_zero] at this
        have h_2b : (2 * b) ≠ 0 := by linarith
        have : a - 2 * ((a + 1) / (2 * b)) * b + ((a + 1) / (2 * b))^2 * 0 ≥ 0 := by linarith
        simp at this
        field_simp at this
        linarith
    rw [h_b_zero, hc_zero]; simp
  · -- c ≠ 0. Since 0 ≤ hessianBilin u w w = c, c > 0.
    have hc_nn : 0 ≤ c := 𝓢.hessianBilin_self_nonneg u hu w
    have hc_pos : 0 < c := lt_of_le_of_ne hc_nn (Ne.symm hc_zero)
    -- Pick λ = b / c.
    have hquad := h_quad_nn (b / c)
    -- Multiply by c > 0: 0 ≤ (a - 2(b/c)b + (b/c)² c) · c = a·c - b².
    have h_mult : 0 ≤ (a - 2 * (b / c) * b + (b / c) ^ 2 * c) * c :=
      mul_nonneg hquad hc_pos.le
    have h_simp : (a - 2 * (b / c) * b + (b / c) ^ 2 * c) * c = a * c - b ^ 2 := by
      have : c ≠ 0 := hc_zero
      field_simp
      ring
    linarith

/-- The `W`-quadratic form `⟨v, W(u) v⟩ = ‖v‖² + ∇²F^*(u)(v, v)`,
where `W(u) = I + ∇²F^*(u)`. Always `≥ ‖v‖²` since the Hessian is PSD. -/
noncomputable def W_quad (u v : H X Y) : ℝ :=
  inner ℝ v v + 𝓢.hessianBilin u v v

/-- `W(u) ⪰ I`: the W-quadratic form dominates the squared Euclidean norm. -/
theorem inner_self_le_W_quad (u : H X Y) (hu : u ∈ 𝓢.C_interior) (v : H X Y) :
    inner ℝ v v ≤ 𝓢.W_quad u v := by
  show inner ℝ v v ≤ inner ℝ v v + 𝓢.hessianBilin u v v
  linarith [𝓢.hessianBilin_self_nonneg u hu v]

/-! ### The `W(u)⁻¹` dual norm -/

/-- The squared dual norm `‖v‖²_{W(u)⁻¹}`, defined via the variational
characterization
    `‖v‖²_{W⁻¹} = sup_{w} ⟨v, w⟩² / W_quad u w`.
Using Lean's `x / 0 = 0` convention at `w = 0`, the sup is over all
`w : H X Y`. For `u ∈ C_interior`, the function being supped is bounded
above by `‖v‖²` (Cauchy-Schwarz + `W(u) ⪰ I`), so the sup is finite. -/
noncomputable def normWinv_sq (𝓢 : IrnSetup X Y) (u v : H X Y) : ℝ :=
  ⨆ w : H X Y, (inner ℝ v w) ^ 2 / 𝓢.W_quad u w

/-- The dual norm `‖·‖_{W(u)⁻¹}`, where `W(u) = I + ∇²F*(u)`.
Defined as the square root of `normWinv_sq`. -/
noncomputable def normWinv (𝓢 : IrnSetup X Y) (u v : H X Y) : ℝ :=
  Real.sqrt (𝓢.normWinv_sq u v)

theorem normWinv_nonneg : ∀ u v, 0 ≤ 𝓢.normWinv u v :=
  fun _ _ => Real.sqrt_nonneg _

/-- The ratio `⟨v, w⟩² / W_quad u w` is bounded above by `‖v‖²`
on `C_interior` (Cauchy-Schwarz + `W(u) ⪰ I`). -/
theorem normWinv_ratio_le_norm_sq (u : H X Y) (hu : u ∈ 𝓢.C_interior)
    (v w : H X Y) : (inner ℝ v w) ^ 2 / 𝓢.W_quad u w ≤ ‖v‖ ^ 2 := by
  by_cases hw : 𝓢.W_quad u w ≤ 0
  · -- W_quad u w ≤ 0; since W_quad ≥ inner v v ≥ 0, this forces equality at 0.
    have h0 : 0 ≤ 𝓢.W_quad u w := le_trans (real_inner_self_nonneg) (𝓢.inner_self_le_W_quad u hu w)
    have heq : 𝓢.W_quad u w = 0 := le_antisymm hw h0
    rw [heq, div_zero]
    exact sq_nonneg _
  · push_neg at hw
    rw [div_le_iff₀ hw]
    -- (⟨v, w⟩)² ≤ ‖v‖² * W_quad u w
    have hCS : (inner ℝ v w) ^ 2 ≤ ‖v‖ ^ 2 * ‖w‖ ^ 2 := by
      have := abs_real_inner_le_norm v w
      nlinarith [sq_nonneg (inner ℝ v w), abs_nonneg (inner ℝ v w),
        sq_abs (inner ℝ v w), norm_nonneg v, norm_nonneg w,
        mul_nonneg (norm_nonneg v) (norm_nonneg w)]
    have h_norm_sq_le : ‖w‖ ^ 2 ≤ 𝓢.W_quad u w := by
      have := 𝓢.inner_self_le_W_quad u hu w
      rwa [real_inner_self_eq_norm_sq] at this
    nlinarith [sq_nonneg ‖v‖, sq_nonneg ‖w‖, norm_nonneg v]

/-- `W(u) ⪰ I` implies `W(u)⁻¹ ⪯ I`, so the dual norm is bounded by
the Euclidean norm. -/
theorem normWinv_le_norm (u : H X Y) (hu : u ∈ 𝓢.C_interior) (v : H X Y) :
    𝓢.normWinv u v ≤ ‖v‖ := by
  unfold normWinv normWinv_sq
  rw [show ‖v‖ = Real.sqrt (‖v‖ ^ 2) from
    (Real.sqrt_sq (norm_nonneg _)).symm]
  apply Real.sqrt_le_sqrt
  exact ciSup_le (fun w => 𝓢.normWinv_ratio_le_norm_sq u hu v w)

theorem normWinv_smul (u : H X Y) (r : ℝ) (v : H X Y) :
    𝓢.normWinv u (r • v) = |r| * 𝓢.normWinv u v := by
  unfold normWinv
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg _)]
  congr 1
  unfold normWinv_sq
  have h_pt : ∀ w : H X Y,
      (inner ℝ (r • v) w) ^ 2 / 𝓢.W_quad u w =
      r ^ 2 * ((inner ℝ v w) ^ 2 / 𝓢.W_quad u w) := by
    intro w
    rw [inner_smul_left, conj_trivial, mul_pow, mul_div_assoc]
  rw [iSup_congr h_pt]
  exact (Real.mul_iSup_of_nonneg (sq_nonneg _) _).symm

/-- **Variational Cauchy-Schwarz bound.** `|⟨v, t⟩| ≤ normWinv u v · √(W_quad u t)`.
This is the contrapositive of the iSup characterization: each ratio
`⟨v, s⟩² / W_quad u s` is `≤ normWinv_sq u v` (by the variational sup),
hence after sqrt and rearrangement. -/
theorem inner_le_normWinv_mul_sqrt_W_quad (u : H X Y) (hu : u ∈ 𝓢.C_interior)
    (v t : H X Y) :
    |inner ℝ v t| ≤ 𝓢.normWinv u v * Real.sqrt (𝓢.W_quad u t) := by
  have hWq_nn : 0 ≤ 𝓢.W_quad u t := by
    have := 𝓢.inner_self_le_W_quad u hu t
    linarith [@real_inner_self_nonneg _ _ _ t]
  have h_bdd : BddAbove (Set.range (fun s : H X Y => (inner ℝ v s) ^ 2 / 𝓢.W_quad u s)) :=
    ⟨‖v‖ ^ 2, by rintro _ ⟨s, rfl⟩; exact 𝓢.normWinv_ratio_le_norm_sq u hu v s⟩
  have h_sq_nn : 0 ≤ 𝓢.normWinv_sq u v := by
    unfold normWinv_sq
    apply le_ciSup_of_le h_bdd 0
    rw [inner_zero_right]; simp
  by_cases hWq_zero : 𝓢.W_quad u t = 0
  · -- t = 0 since ‖t‖² ≤ W_quad u t = 0.
    have h_t_norm_sq : ‖t‖ ^ 2 ≤ 0 := by
      have h := 𝓢.inner_self_le_W_quad u hu t
      rw [real_inner_self_eq_norm_sq, hWq_zero] at h
      exact h
    have h_t_zero : t = 0 := by
      have h_t_norm : ‖t‖ = 0 := by nlinarith [sq_nonneg ‖t‖]
      exact norm_eq_zero.mp h_t_norm
    rw [h_t_zero, inner_zero_right, abs_zero]
    exact mul_nonneg (𝓢.normWinv_nonneg u v) (Real.sqrt_nonneg _)
  · have hWq_pos : 0 < 𝓢.W_quad u t := lt_of_le_of_ne hWq_nn (Ne.symm hWq_zero)
    have h_ratio : (inner ℝ v t) ^ 2 / 𝓢.W_quad u t ≤ 𝓢.normWinv_sq u v :=
      le_ciSup h_bdd t
    have h_sq : (inner ℝ v t) ^ 2 ≤ 𝓢.normWinv_sq u v * 𝓢.W_quad u t := by
      rw [← div_le_iff₀ hWq_pos]; exact h_ratio
    have h_RHS_sq : (𝓢.normWinv u v * Real.sqrt (𝓢.W_quad u t)) ^ 2 =
        𝓢.normWinv_sq u v * 𝓢.W_quad u t := by
      rw [mul_pow]
      unfold normWinv
      rw [Real.sq_sqrt h_sq_nn, Real.sq_sqrt hWq_nn]
    have h_RHS_nn : 0 ≤ 𝓢.normWinv u v * Real.sqrt (𝓢.W_quad u t) :=
      mul_nonneg (𝓢.normWinv_nonneg u v) (Real.sqrt_nonneg _)
    have h_abs_sq : |inner ℝ v t| ^ 2 ≤ (𝓢.normWinv u v * Real.sqrt (𝓢.W_quad u t)) ^ 2 := by
      rw [sq_abs, h_RHS_sq]; exact h_sq
    exact abs_le_of_sq_le_sq' h_abs_sq h_RHS_nn |>.2

/-- Triangle inequality for `normWinv`. From the variational CS bound
`|⟨v, t⟩| ≤ normWinv u v · √(W_quad u t)`, the bound transfers to
`v + w` via the triangle for `|·|`, then sup over `t`. -/
theorem normWinv_triangle (u : H X Y) (hu : u ∈ 𝓢.C_interior)
    (v w : H X Y) :
    𝓢.normWinv u (v + w) ≤ 𝓢.normWinv u v + 𝓢.normWinv u w := by
  -- Squared bound: for each t, ⟨v+w, t⟩²/W_quad u t ≤ (normWinv v + normWinv w)².
  have hN_v_nn : 0 ≤ 𝓢.normWinv u v := 𝓢.normWinv_nonneg u v
  have hN_w_nn : 0 ≤ 𝓢.normWinv u w := 𝓢.normWinv_nonneg u w
  have h_pt : ∀ t : H X Y,
      (inner ℝ (v + w) t) ^ 2 / 𝓢.W_quad u t ≤
        (𝓢.normWinv u v + 𝓢.normWinv u w) ^ 2 := by
    intro t
    have hWq_nn : 0 ≤ 𝓢.W_quad u t := by
      have := 𝓢.inner_self_le_W_quad u hu t
      linarith [@real_inner_self_nonneg _ _ _ t]
    by_cases hWq_zero : 𝓢.W_quad u t = 0
    · rw [hWq_zero, div_zero]
      positivity
    · have hWq_pos : 0 < 𝓢.W_quad u t := lt_of_le_of_ne hWq_nn (Ne.symm hWq_zero)
      rw [div_le_iff₀ hWq_pos]
      have h_v := 𝓢.inner_le_normWinv_mul_sqrt_W_quad u hu v t
      have h_w := 𝓢.inner_le_normWinv_mul_sqrt_W_quad u hu w t
      have h_tri : |inner ℝ (v + w) t| ≤
          (𝓢.normWinv u v + 𝓢.normWinv u w) * Real.sqrt (𝓢.W_quad u t) := by
        rw [inner_add_left]
        calc |inner ℝ v t + inner ℝ w t|
            ≤ |inner ℝ v t| + |inner ℝ w t| := abs_add_le _ _
          _ ≤ 𝓢.normWinv u v * Real.sqrt (𝓢.W_quad u t) +
              𝓢.normWinv u w * Real.sqrt (𝓢.W_quad u t) := by linarith
          _ = (𝓢.normWinv u v + 𝓢.normWinv u w) * Real.sqrt (𝓢.W_quad u t) := by ring
      have h_RHS_nn : 0 ≤ (𝓢.normWinv u v + 𝓢.normWinv u w) * Real.sqrt (𝓢.W_quad u t) :=
        mul_nonneg (add_nonneg hN_v_nn hN_w_nn) (Real.sqrt_nonneg _)
      have h_sq_tri : (inner ℝ (v + w) t) ^ 2 ≤
          ((𝓢.normWinv u v + 𝓢.normWinv u w) * Real.sqrt (𝓢.W_quad u t)) ^ 2 := by
        rw [← sq_abs (inner _ _ _)]
        exact pow_le_pow_left₀ (abs_nonneg _) h_tri 2
      calc (inner ℝ (v + w) t) ^ 2
          ≤ ((𝓢.normWinv u v + 𝓢.normWinv u w) * Real.sqrt (𝓢.W_quad u t)) ^ 2 := h_sq_tri
        _ = (𝓢.normWinv u v + 𝓢.normWinv u w) ^ 2 * 𝓢.W_quad u t := by
            rw [mul_pow, Real.sq_sqrt hWq_nn]
  have h_sq_bound : 𝓢.normWinv_sq u (v + w) ≤
      (𝓢.normWinv u v + 𝓢.normWinv u w) ^ 2 := by
    unfold normWinv_sq
    exact ciSup_le h_pt
  have h_sum_nn : 0 ≤ 𝓢.normWinv u v + 𝓢.normWinv u w :=
    add_nonneg hN_v_nn hN_w_nn
  calc 𝓢.normWinv u (v + w)
      = Real.sqrt (𝓢.normWinv_sq u (v + w)) := rfl
    _ ≤ Real.sqrt ((𝓢.normWinv u v + 𝓢.normWinv u w) ^ 2) :=
        Real.sqrt_le_sqrt h_sq_bound
    _ = 𝓢.normWinv u v + 𝓢.normWinv u w := Real.sqrt_sq h_sum_nn

/-- **LHSCB gradient bound** (paper §3.2):
`‖φ(u)‖²_{W(u)⁻¹} ≤ ν + 1`, hence `‖φ(u)‖_{W(u)⁻¹} ≤ √(ν+1)`. The
proof uses the chain
  `⟨φ u, t⟩² = (hessianBilin u u t)²        [hessianBilin_apply_self]
            ≤ hessianBilin u u u · hessianBilin u t t  [hessianBilin_CS]
            = (ν + 1) · hessianBilin u t t   [hessianBilin_self_self]
            ≤ (ν + 1) · W_quad u t           [W_quad ≥ hessianBilin]`
hence `⟨φ u, t⟩² / W_quad u t ≤ ν + 1` after division, and the iSup
preserves this. -/
theorem normWinv_phi_bound : ∀ u ∈ 𝓢.C_interior,
    𝓢.normWinv u (𝓢.φ u) ≤ Real.sqrt ((𝓢.ν : ℝ) + 1) := by
  intro u hu
  -- Pointwise bound on each ratio.
  have h_pt : ∀ t : H X Y,
      (inner ℝ (𝓢.φ u) t) ^ 2 / 𝓢.W_quad u t ≤ (𝓢.ν : ℝ) + 1 := by
    intro t
    have hWq_nn : 0 ≤ 𝓢.W_quad u t := by
      have := 𝓢.inner_self_le_W_quad u hu t
      linarith [@real_inner_self_nonneg _ _ _ t]
    have hH_tt_nn : 0 ≤ 𝓢.hessianBilin u t t := 𝓢.hessianBilin_self_nonneg u hu t
    have hH_tt_le : 𝓢.hessianBilin u t t ≤ 𝓢.W_quad u t := by
      show 𝓢.hessianBilin u t t ≤ inner ℝ t t + 𝓢.hessianBilin u t t
      linarith [@real_inner_self_nonneg _ _ _ t]
    -- ⟨φ u, t⟩ = -hessianBilin u u t.
    have h_inner_eq : inner ℝ (𝓢.φ u) t = -𝓢.hessianBilin u u t := by
      rw [real_inner_comm, 𝓢.hessianBilin_apply_self u hu t]
      ring
    have h_sq_eq : (inner ℝ (𝓢.φ u) t) ^ 2 = (𝓢.hessianBilin u u t) ^ 2 := by
      rw [h_inner_eq, neg_pow_two]
    have h_CS : (𝓢.hessianBilin u u t) ^ 2 ≤
        𝓢.hessianBilin u u u * 𝓢.hessianBilin u t t :=
      𝓢.hessianBilin_CS u hu u t
    have h_self_self : 𝓢.hessianBilin u u u = (𝓢.ν : ℝ) + 1 :=
      𝓢.hessianBilin_self_self u hu
    have h_main : (inner ℝ (𝓢.φ u) t) ^ 2 ≤ ((𝓢.ν : ℝ) + 1) * 𝓢.W_quad u t := by
      calc (inner ℝ (𝓢.φ u) t) ^ 2
          = (𝓢.hessianBilin u u t) ^ 2 := h_sq_eq
        _ ≤ 𝓢.hessianBilin u u u * 𝓢.hessianBilin u t t := h_CS
        _ = ((𝓢.ν : ℝ) + 1) * 𝓢.hessianBilin u t t := by rw [h_self_self]
        _ ≤ ((𝓢.ν : ℝ) + 1) * 𝓢.W_quad u t := by
            apply mul_le_mul_of_nonneg_left hH_tt_le
            have : (0 : ℝ) ≤ (𝓢.ν : ℝ) := Nat.cast_nonneg _
            linarith
    by_cases hWq_zero : 𝓢.W_quad u t = 0
    · rw [hWq_zero, div_zero]
      have : (0 : ℝ) ≤ (𝓢.ν : ℝ) := Nat.cast_nonneg _
      linarith
    · have hWq_pos : 0 < 𝓢.W_quad u t := lt_of_le_of_ne hWq_nn (Ne.symm hWq_zero)
      rw [div_le_iff₀ hWq_pos]
      exact h_main
  -- Conclude via ciSup and sqrt.
  have h_sq_bound : 𝓢.normWinv_sq u (𝓢.φ u) ≤ (𝓢.ν : ℝ) + 1 := by
    unfold normWinv_sq
    exact ciSup_le h_pt
  unfold normWinv
  have h_nu1_nn : (0 : ℝ) ≤ (𝓢.ν : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (𝓢.ν : ℝ) := Nat.cast_nonneg _; linarith
  exact Real.sqrt_le_sqrt h_sq_bound

/-! ### Hessian preconditioner -/

/-- The Hessian operator `∇²F^*(u) : H →L H` at `u`, viewed as a CLM
via Riesz representation. On `C_interior`, this satisfies
`⟨v, hess_op u w⟩ = hessianBilin u v w`. -/
noncomputable def hess_op (𝓢 : IrnSetup X Y) (u : H X Y) :
    H X Y →L[ℝ] H X Y :=
  (InnerProductSpace.toDual ℝ (H X Y)).symm.toContinuousLinearMap.comp
    (fderiv ℝ (fderiv ℝ 𝓢.F_lhscb.f) u)

/-- The W operator `W(u) = I + ∇²F^*(u)`. -/
noncomputable def W_op (𝓢 : IrnSetup X Y) (u : H X Y) :
    H X Y →L[ℝ] H X Y :=
  ContinuousLinearMap.id ℝ (H X Y) + 𝓢.hess_op u

/-- The Hessian preconditioner `H_k = ∇h(u_k) = μI + μ∇²F^*(u_k) = μ W(u)`
(paper §5.2). -/
noncomputable def hessian_h (𝓢 : IrnSetup X Y) (μ : ℝ) (u : H X Y) :
    H X Y →L[ℝ] H X Y :=
  μ • 𝓢.W_op u

/-- **Riesz characterization of `hess_op`.** On `C_interior`,
`⟨v, hess_op u w⟩ = (fderiv (fderiv F_lhscb.f) u) w v = hessianBilin u w v`. -/
theorem hess_op_apply_inner (u : H X Y) (hu : u ∈ 𝓢.C_interior) (v w : H X Y) :
    inner ℝ v (𝓢.hess_op u w) = 𝓢.hessianBilin u w v := by
  show inner ℝ v
    ((InnerProductSpace.toDual ℝ (H X Y)).symm
      ((fderiv ℝ (fderiv ℝ 𝓢.F_lhscb.f) u) w)) = _
  rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
  rw [𝓢.hessianBilin_eq_fderiv u hu w v]

/-- The W-operator's inner product: `⟨v, W_op u w⟩ = ⟨v, w⟩ + hessianBilin u w v`.
With symmetry, the second term is `hessianBilin u v w`. -/
theorem W_op_apply_inner (u : H X Y) (hu : u ∈ 𝓢.C_interior) (v w : H X Y) :
    inner ℝ v (𝓢.W_op u w) = inner ℝ v w + 𝓢.hessianBilin u w v := by
  show inner ℝ v (w + 𝓢.hess_op u w) = _
  rw [inner_add_right, 𝓢.hess_op_apply_inner u hu]

/-- The W-quadratic form computed via the operator:
`⟨v, W_op u v⟩ = W_quad u v`. -/
theorem inner_self_W_op_eq_W_quad (u : H X Y) (hu : u ∈ 𝓢.C_interior) (v : H X Y) :
    inner ℝ v (𝓢.W_op u v) = 𝓢.W_quad u v := by
  rw [𝓢.W_op_apply_inner u hu]
  show inner ℝ v v + 𝓢.hessianBilin u v v = inner ℝ v v + 𝓢.hessianBilin u v v
  rfl

/-- The underlying CLM `μ W(u) + M` (without the equivalence packaging). -/
noncomputable def hessian_plus_M_op (𝓢 : IrnSetup X Y) (μ : ℝ) (u : H X Y) :
    H X Y →L[ℝ] H X Y :=
  𝓢.hessian_h μ u + 𝓢.M_clm

/-- The inner product `⟨v, (μ W + M) v⟩` lower bound on `C_interior`:
`μ ‖v‖²` (using `W ⪰ I` and `inner_u_M ≥ 0`). -/
lemma inner_self_hessian_plus_M_op_lower (μ : ℝ) (hμ : 0 < μ)
    (u : H X Y) (hu : u ∈ 𝓢.C_interior) (v : H X Y) :
    μ * ‖v‖ ^ 2 ≤ inner ℝ v (𝓢.hessian_plus_M_op μ u v) := by
  show μ * ‖v‖ ^ 2 ≤ inner ℝ v (𝓢.hessian_h μ u v + 𝓢.M_clm v)
  rw [inner_add_right]
  have h_h : inner ℝ v (𝓢.hessian_h μ u v) = μ * 𝓢.W_quad u v := by
    show inner ℝ v (μ • 𝓢.W_op u v) = _
    rw [inner_smul_right, 𝓢.inner_self_W_op_eq_W_quad u hu]
  have h_M : inner ℝ v (𝓢.M_clm v) = 𝓢.Px_bilinform (𝓢.x_proj v) (𝓢.x_proj v) := by
    show inner ℝ v (𝓢.M_apply v) = _
    exact 𝓢.inner_u_M v
  rw [h_h, h_M]
  have h_Px_nn : 0 ≤ 𝓢.Px_bilinform (𝓢.x_proj v) (𝓢.x_proj v) :=
    𝓢.Px_bilinform_self_nonneg _
  have h_W_ge : ‖v‖ ^ 2 ≤ 𝓢.W_quad u v := by
    have := 𝓢.inner_self_le_W_quad u hu v
    rwa [real_inner_self_eq_norm_sq] at this
  nlinarith

/-- `hessian_plus_M_op` is injective on `C_interior` for `μ > 0`. -/
lemma hessian_plus_M_op_injective (μ : ℝ) (hμ : 0 < μ)
    (u : H X Y) (hu : u ∈ 𝓢.C_interior) :
    Function.Injective (𝓢.hessian_plus_M_op μ u) := by
  intro v₁ v₂ hv
  -- (T (v₁ - v₂)) = 0
  have h_zero : 𝓢.hessian_plus_M_op μ u (v₁ - v₂) = 0 := by
    rw [map_sub, hv, sub_self]
  by_contra hne
  have hv_ne : v₁ - v₂ ≠ 0 := sub_ne_zero.mpr hne
  have h_lower := 𝓢.inner_self_hessian_plus_M_op_lower μ hμ u hu (v₁ - v₂)
  rw [h_zero, inner_zero_right] at h_lower
  have h_norm_pos : 0 < ‖v₁ - v₂‖ ^ 2 := by
    have : 0 < ‖v₁ - v₂‖ := norm_pos_iff.mpr hv_ne
    positivity
  nlinarith

/-- The continuous linear equivalence `H_k + M`. Invertible because its
symmetric part is `μ W(u) ≻ 0` (positive definite for `μ > 0`,
`u ∈ C_interior`). Currently sorried — `hessian_plus_M_op_injective`
provides the injectivity; combining with `LinearMap.injective_iff_surjective`
in finite-dim gives bijectivity, hence a CLE. The wrapping into the
existing unconditional API (which the downstream `exists_pos_root_quad`
in `Resolvent.lean` consumes without the `u ∈ C_interior` hypothesis)
requires API restructuring; deferred. -/
noncomputable def hessian_plus_M (_ : IrnSetup X Y) :
    ℝ → H X Y → (H X Y ≃L[ℝ] H X Y) := sorry

theorem hessian_plus_M_eq : ∀ μ u v,
    (𝓢.hessian_plus_M μ u : H X Y →L[ℝ] H X Y) v =
      𝓢.hessian_h μ u v + 𝓢.M_clm v := sorry

/-! ### Riemannian Josephy–Newton corrector and multiplier -/

/-- The Riemannian Josephy–Newton corrector (paper eq. (5.3), Variant A).
Computed via the closed-form resolvent at the `λ`-shifted input of
eq. (5.4). -/
noncomputable def rjnStep (_ : IrnSetup X Y) : ℝ → H X Y → H X Y := sorry

/-- The sphere-constraint Lagrange multiplier (paper Proposition 11). -/
noncomputable def rjnLambda (_ : IrnSetup X Y) : ℝ → H X Y → ℝ := sorry

/-- **Proposition 11 (Existence of `λ_k`).** `rjnLambda μ` evaluates to
`0` at central-path points. -/
theorem rjnLambda_at_central : ∀ μ : ℝ, ∀ u : H X Y, 0 < μ →
    u ∈ 𝓢.C_interior →
    𝓢.Q u + μ • u + μ • 𝓢.φ u = 0 → 𝓢.rjnLambda μ u = 0 := sorry

/-- **Proposition 11 (continued).** `rjnLambda μ` is continuous at the
central-path point. -/
theorem rjnLambda_continuousAt_central : ∀ μ : ℝ, ∀ u : H X Y, 0 < μ →
    u ∈ 𝓢.C_interior →
    𝓢.Q u + μ • u + μ • 𝓢.φ u = 0 →
    ContinuousAt (𝓢.rjnLambda μ) u := sorry

/-- The corrector preserves the squared-norm constraint `‖u‖² = ν + 1`
(the sphere `Sr`). -/
theorem rjnStep_norm_sq : ∀ μ : ℝ, ∀ u : H X Y, 0 < μ →
    ‖u‖ ^ 2 = (𝓢.ν : ℝ) + 1 → u ∈ 𝓢.C_interior →
    ‖𝓢.rjnStep μ u‖ ^ 2 = (𝓢.ν : ℝ) + 1 := sorry

/-- The corrector preserves the interior cone `int C`. -/
theorem rjnStep_in_C : ∀ μ : ℝ, ∀ u : H X Y, 0 < μ →
    ‖u‖ ^ 2 = (𝓢.ν : ℝ) + 1 → u ∈ 𝓢.C_interior →
    𝓢.rjnStep μ u ∈ 𝓢.C_interior := sorry

/-! ### Minty's resolvent existence -/

/-- **Minty's theorem applied to `H_k + Ψ`.** The augmented Newton
inclusion has a positive scalar `θ` and a primal `u ∈ C_+`. -/
theorem resolvent_exists : ∀ μ : ℝ, ∀ u_k z : H X Y, 0 < μ →
    ∃ u : H X Y, u ∈ 𝓢.Cplus ∧ ∃ θ : ℝ, 0 < θ ∧
      (𝓢.hessian_h μ u_k + 𝓢.M_clm) u = 𝓢.hessian_h μ u_k z + θ • 𝓢.e_τ ∧
      θ * 𝓢.tau_proj u = 𝓢.Px_bilinform_clm u u + μ := sorry

/-! ### Newton–Kantorovich contractions -/

/-- **Lemma 15 (Hessian-norm Newton–Kantorovich).** On `Sr ∩ C_interior`,
one corrector step contracts `δ = ‖T‖_{W⁻¹}/μ` quadratically with
basin radius `ρ_star` and rate `K_star`. -/
theorem rjnStep_delta_contraction : ∃ ρ_star K_star : ℝ,
    0 < ρ_star ∧ ρ_star < 1 ∧ 1 ≤ K_star ∧
    ∀ μ : ℝ, 0 < μ → ∀ u : H X Y,
      ‖u‖ ^ 2 = (𝓢.ν : ℝ) + 1 → u ∈ 𝓢.C_interior →
      𝓢.normWinv u (𝓢.Q u + μ • u + μ • 𝓢.φ u) / μ ≤ ρ_star →
      𝓢.normWinv (𝓢.rjnStep μ u)
          (𝓢.Q (𝓢.rjnStep μ u) + μ • (𝓢.rjnStep μ u) +
            μ • 𝓢.φ (𝓢.rjnStep μ u)) / μ ≤
        K_star *
          (𝓢.normWinv u (𝓢.Q u + μ • u + μ • 𝓢.φ u) / μ) ^ 2 := sorry

/-- **Theorem 12 (Euclidean Newton–Kantorovich).** Near each
central-path point, there is an open `U` and a rate `K` such that the
corrector stays in `U` and contracts the Euclidean error quadratically. -/
theorem rjnStep_euclidean_basin : ∀ μ : ℝ, 0 < μ → ∀ u_star : H X Y,
    u_star ∈ 𝓢.C_interior →
    𝓢.Q u_star + μ • u_star + μ • 𝓢.φ u_star = 0 →
    ∃ U : Set (H X Y), IsOpen U ∧ u_star ∈ U ∧
      ∃ K : ℝ, 0 < K ∧
      (∀ u ∈ U, ‖u‖ ^ 2 = (𝓢.ν : ℝ) + 1 → u ∈ 𝓢.C_interior →
         𝓢.rjnStep μ u ∈ U) ∧
      (∀ u ∈ U, ‖u‖ ^ 2 = (𝓢.ν : ℝ) + 1 → u ∈ 𝓢.C_interior →
         ‖𝓢.rjnStep μ u - u_star‖ ≤ K * ‖u - u_star‖ ^ 2) := sorry

end IrnSetup
end Irn
