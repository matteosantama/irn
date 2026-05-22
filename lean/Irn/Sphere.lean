/-
# Sphere geometry, tangentiality, error bound (paper §3, §5.3)

The sphere `Sr ⊆ H`, the orthogonal projector `P_u` onto the tangent
space, the tangentiality lemma, the a-posteriori error bound, and the
closed-form geodesic exponential of `Sr`.

Paper references:
* §3.1 (geometry)
* §3.1 Lemma 5 (tangentiality) → `tangent_T`
* §3.3 Theorem 8 (a posteriori error bound) → `error_bound`,
  `error_bound_tangent`
* §5.3 eq. `eq:retraction` (geodesic exp) → `expMap`
* §5.3 Proposition 10 (exact sphericity of `exp_u`) → `expMap_mem_sphere`
-/

import Irn.CentralPath
import Irn.Analytic

namespace Irn

open scoped InnerProductSpace

section Projector

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The orthogonal projector onto `u^⊥` in `H` (the tangent space to
the sphere through `u`, when `u ≠ 0`).  We use the totalised formula
`P_u v = v - (⟨u, v⟩ / ‖u‖²) • u`, which at `u = 0` returns `v` because
division by zero is zero in `ℝ`. -/
noncomputable def proj (u v : H) : H :=
  v - (inner ℝ u v / ‖u‖ ^ 2) • u

/-- If `v ⟂ u` in the Euclidean sense, the projector fixes `v`. -/
theorem proj_of_orthogonal (u v : H) (h : inner ℝ u v = (0 : ℝ)) :
    proj u v = v := by
  unfold proj
  rw [h, zero_div, zero_smul, sub_zero]

end Projector

namespace IrnSetup

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  (𝓢 : IrnSetup X Y)

/-- The sphere `Sr = { u : ‖u‖ = r }`. -/
def sphere : Set (H X Y) := {u | ‖u‖ = 𝓢.r}

/-! ### Geodesic exponential map on `Sr` (paper §7.1)

The round sphere `Sr` of radius `r` has a closed-form Riemannian
exponential map (paper eq. `eq:exp-map`):
`exp_u(v) = cos(‖v‖/r) · u + r · sin(‖v‖/r)/‖v‖ · v`
for `v ∈ T_u Sr`, with the convention `exp_u(0) = u`. -/

/-- The geodesic exp map at `u` on the sphere `Sr` of radius `r`, in
closed form. The base formula
`cos(‖v‖/r) • u + r·sin(‖v‖/r)/‖v‖ • v`
has a removable `0/0` singularity at `v = 0`; for that case
Lean's `0⁻¹ = 0` convention turns the second term into `0`, leaving
`cos 0 • u = u` — so the closed form is correct on all of `H X Y`. For
`v ∈ T_u Sr` the result lies on `Sr` (see `expMap_mem_sphere`). -/
noncomputable def expMap (𝓢 : IrnSetup X Y) (u v : H X Y) : H X Y :=
  Real.cos (‖v‖ / 𝓢.r) • u + (𝓢.r * Real.sin (‖v‖ / 𝓢.r) / ‖v‖) • v

@[simp] theorem expMap_zero (u : H X Y) : 𝓢.expMap u 0 = u := by
  show Real.cos (‖(0 : H X Y)‖ / 𝓢.r) • u +
      (𝓢.r * Real.sin (‖(0 : H X Y)‖ / 𝓢.r) / ‖(0 : H X Y)‖) • (0 : H X Y) = u
  simp

/-- **Proposition 10 (Exact sphericity of `exp_u`).** For `u ∈ Sr` and
`v ⟂ u` in the Euclidean sense, `exp_u(v) ∈ Sr`. Orthogonality kills
the cross term in `‖a u + b v‖²`, and `cos² + sin² = 1` recovers `r²`.
Handles `v = 0` via `expMap_zero`. Sorry-free. -/
theorem expMap_mem_sphere (u v : H X Y) (hu : u ∈ 𝓢.sphere)
    (hv : inner ℝ u v = (0 : ℝ)) :
    𝓢.expMap u v ∈ 𝓢.sphere := by
  have hr_pos : 0 < 𝓢.r := 𝓢.r_pos
  have h_u_norm : ‖u‖ = 𝓢.r := hu
  show ‖𝓢.expMap u v‖ = 𝓢.r
  by_cases hv0 : v = 0
  · rw [hv0, 𝓢.expMap_zero]; exact h_u_norm
  have hvn : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv0
  set t : ℝ := ‖v‖ / 𝓢.r
  set a : ℝ := Real.cos t
  set b : ℝ := 𝓢.r * Real.sin t / ‖v‖
  -- ‖a u + b v‖² = a² ‖u‖² + b² ‖v‖² (cross term ⟨u, v⟩ vanishes).
  have h_cross_zero : inner ℝ (a • u) (b • v) = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right, hv]; ring
  have h_cross_zero_flipped : inner ℝ (b • v) (a • u) = 0 := by
    rw [real_inner_comm]; exact h_cross_zero
  have h_norm_add_sq : ‖a • u + b • v‖ ^ 2 = ‖a • u‖ ^ 2 + ‖b • v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
        inner_add_right, h_cross_zero, h_cross_zero_flipped,
        ← real_inner_self_eq_norm_sq (a • u),
        ← real_inner_self_eq_norm_sq (b • v)]
    ring
  have h_a_sq : ‖a • u‖ ^ 2 = a ^ 2 * 𝓢.r ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, h_u_norm]
  have h_b_sq : ‖b • v‖ ^ 2 = 𝓢.r ^ 2 * Real.sin t ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    show (𝓢.r * Real.sin t / ‖v‖) ^ 2 * ‖v‖ ^ 2 = _
    field_simp
  have h_sq : ‖𝓢.expMap u v‖ ^ 2 = 𝓢.r ^ 2 := by
    show ‖a • u + b • v‖ ^ 2 = _
    rw [h_norm_add_sq, h_a_sq, h_b_sq]
    -- Goal: a² * r² + r² * sin²t = r², with a = cos t.
    have h_pyth : Real.cos t ^ 2 + Real.sin t ^ 2 = 1 := Real.cos_sq_add_sin_sq t
    show Real.cos t ^ 2 * 𝓢.r ^ 2 + 𝓢.r ^ 2 * Real.sin t ^ 2 = 𝓢.r ^ 2
    nlinarith [h_pyth]
  nlinarith [h_sq, norm_nonneg (𝓢.expMap u v), hr_pos]

/-! ### Second-order retraction property of `expMap`

The geodesic retraction `expMap` agrees with the tangent point
`u + v` to first order; the discrepancy is `O(‖v‖²)`. This is the
"second-order retraction" property in Absil's sense and the
*retraction half* of the local quadratic convergence theorem (paper
§5.6 Theorem 12). Proven from the closed-form trig identities and
the bounds `|1 − cos t| ≤ t²/2`, `|sin t − t| ≤ t³/4` (the latter
holds on `(0, 1]` via `Real.sin_gt_sub_cube`). -/

/-- Algebraic identity for `expMap u v − (u + v)` in terms of `cos`
and `sin/t`: writes the diff as `(cos t − 1) • u + (sin t / t − 1) • v`,
which is what the proof of `expMap_sub_add_norm_le` operates on. -/
private theorem expMap_sub_add_eq {u v : H X Y} (hv0 : v ≠ 0) :
    𝓢.expMap u v - (u + v) =
      (Real.cos (‖v‖ / 𝓢.r) - 1) • u +
        (Real.sin (‖v‖ / 𝓢.r) / (‖v‖ / 𝓢.r) - 1) • v := by
  have hr_pos : 0 < 𝓢.r := 𝓢.r_pos
  have h_v_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have h_v_ne : ‖v‖ ≠ 0 := ne_of_gt h_v_norm_pos
  have hr_ne : 𝓢.r ≠ 0 := ne_of_gt hr_pos
  have h_b_eq : 𝓢.r * Real.sin (‖v‖ / 𝓢.r) / ‖v‖ =
      Real.sin (‖v‖ / 𝓢.r) / (‖v‖ / 𝓢.r) := by
    field_simp
  show Real.cos (‖v‖ / 𝓢.r) • u +
        (𝓢.r * Real.sin (‖v‖ / 𝓢.r) / ‖v‖) • v - (u + v) =
      (Real.cos (‖v‖ / 𝓢.r) - 1) • u +
        (Real.sin (‖v‖ / 𝓢.r) / (‖v‖ / 𝓢.r) - 1) • v
  rw [h_b_eq, sub_smul, sub_smul, one_smul, one_smul]
  abel

/-- **Retraction quadratic remainder.** For `u ∈ Sr` and `v ⟂ u` with
`‖v‖ ≤ r`, the geodesic retraction `expMap u v` differs from the
tangent point `u + v` by at most `‖v‖² / r` in Euclidean norm. The
constant `1` is loose (the sharp constant is `√(5)/4 ≈ 0.559`); we
keep the simpler form. This is the retraction half of paper §5.6
Theorem 12. -/
theorem expMap_sub_add_norm_le {u v : H X Y}
    (hu : u ∈ 𝓢.sphere) (hv : inner ℝ u v = (0 : ℝ))
    (hv_le : ‖v‖ ≤ 𝓢.r) :
    ‖𝓢.expMap u v - (u + v)‖ ≤ ‖v‖ ^ 2 / 𝓢.r := by
  have hr_pos : 0 < 𝓢.r := 𝓢.r_pos
  have hr_ne : 𝓢.r ≠ 0 := ne_of_gt hr_pos
  have h_u_norm : ‖u‖ = 𝓢.r := hu
  by_cases hv0 : v = 0
  · simp [hv0, 𝓢.expMap_zero]
  have h_v_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have h_v_ne : ‖v‖ ≠ 0 := ne_of_gt h_v_norm_pos
  set t : ℝ := ‖v‖ / 𝓢.r with ht_def
  have ht_pos : 0 < t := div_pos h_v_norm_pos hr_pos
  have ht_le_one : t ≤ 1 := by rw [ht_def, div_le_one hr_pos]; exact hv_le
  have ht_ne : t ≠ 0 := ne_of_gt ht_pos
  set α : ℝ := Real.cos t - 1 with hα_def
  set β : ℝ := Real.sin t / t - 1 with hβ_def
  have h_diff : 𝓢.expMap u v - (u + v) = α • u + β • v := 𝓢.expMap_sub_add_eq hv0
  -- ‖α u + β v‖² = α² ‖u‖² + β² ‖v‖² (orthogonality).
  have h_cross : inner ℝ (α • u) (β • v) = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right, hv]; ring
  have h_cross_flip : inner ℝ (β • v) (α • u) = 0 := by
    rw [real_inner_comm]; exact h_cross
  have h_norm_sq : ‖α • u + β • v‖ ^ 2 = α ^ 2 * 𝓢.r ^ 2 + β ^ 2 * ‖v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
        inner_add_right, h_cross, h_cross_flip]
    rw [real_inner_smul_left, real_inner_smul_left,
        real_inner_smul_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq u, real_inner_self_eq_norm_sq v, h_u_norm]
    ring
  -- Bound α² ≤ (t²/2)² = t⁴/4 via |1 - cos t| ≤ t²/2.
  have h_α_sq_le : α ^ 2 ≤ t ^ 4 / 4 := by
    have h_cos := Real.one_sub_sq_div_two_le_cos (x := t)
    have h_cos_le_one : Real.cos t ≤ 1 := Real.cos_le_one t
    have h_α_abs : |α| ≤ t ^ 2 / 2 := by
      rw [hα_def, abs_le]
      constructor
      · linarith
      · linarith
    have : α ^ 2 = |α| ^ 2 := (sq_abs α).symm
    rw [this]
    have : (t ^ 2 / 2) ^ 2 = t ^ 4 / 4 := by ring
    rw [← this]
    exact pow_le_pow_left₀ (abs_nonneg _) h_α_abs 2
  -- Bound β² · ‖v‖² ≤ (t³/4)² · r² = t⁶ · r² / 16, then translate to ‖v‖.
  -- Step: β · ‖v‖ = (sin t/t - 1) · t · r = ((sin t - t)/t) · t · r = (sin t - t) · r.
  -- So (β · ‖v‖)² = (sin t - t)² · r².
  -- Using sin t ≤ t (Real.sin_le) and x - x³/4 < sin x (Real.sin_gt_sub_cube),
  -- 0 ≤ t - sin t < t³/4 for t ∈ (0, 1], hence (sin t - t)² < t⁶/16.
  have h_β_v_sq : β ^ 2 * ‖v‖ ^ 2 = (Real.sin t - t) ^ 2 * 𝓢.r ^ 2 := by
    have h_β_v : β * ‖v‖ = (Real.sin t - t) * 𝓢.r := by
      rw [hβ_def, ht_def]; field_simp
    have h_sq : (β * ‖v‖) ^ 2 = ((Real.sin t - t) * 𝓢.r) ^ 2 := by rw [h_β_v]
    rw [show β ^ 2 * ‖v‖ ^ 2 = (β * ‖v‖) ^ 2 from by ring,
        show (Real.sin t - t) ^ 2 * 𝓢.r ^ 2 = ((Real.sin t - t) * 𝓢.r) ^ 2 from by ring]
    exact h_sq
  have h_sin_sub_t_abs : |Real.sin t - t| ≤ t ^ 3 / 4 := by
    have h_sin_le : Real.sin t ≤ t := Real.sin_le ht_pos.le
    have h_t_sub_sin : t - Real.sin t < t ^ 3 / 4 := by
      have := Real.sin_gt_sub_cube ht_pos ht_le_one
      linarith
    rw [abs_le]
    constructor
    · linarith
    · have : Real.sin t - t ≤ 0 := by linarith
      have : t ^ 3 / 4 ≥ 0 := by positivity
      linarith
  have h_sin_sub_sq_le : (Real.sin t - t) ^ 2 ≤ t ^ 6 / 16 := by
    have h : |Real.sin t - t| ^ 2 ≤ (t ^ 3 / 4) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h_sin_sub_t_abs 2
    have h_lhs : |Real.sin t - t| ^ 2 = (Real.sin t - t) ^ 2 := sq_abs _
    have h_rhs : (t ^ 3 / 4) ^ 2 = t ^ 6 / 16 := by ring
    linarith
  have hr_sq_nn : 0 ≤ 𝓢.r ^ 2 := sq_nonneg _
  have h_β_v_le : β ^ 2 * ‖v‖ ^ 2 ≤ t ^ 6 * 𝓢.r ^ 2 / 16 := by
    rw [h_β_v_sq]
    have h_t6_r2_eq : t ^ 6 * 𝓢.r ^ 2 / 16 = (t ^ 6 / 16) * 𝓢.r ^ 2 := by ring
    rw [h_t6_r2_eq]
    exact mul_le_mul_of_nonneg_right h_sin_sub_sq_le hr_sq_nn
  have h_α_sq_r_le : α ^ 2 * 𝓢.r ^ 2 ≤ t ^ 4 * 𝓢.r ^ 2 / 4 := by
    have h_t4_r2_eq : t ^ 4 * 𝓢.r ^ 2 / 4 = (t ^ 4 / 4) * 𝓢.r ^ 2 := by ring
    rw [h_t4_r2_eq]
    exact mul_le_mul_of_nonneg_right h_α_sq_le hr_sq_nn
  have ht_sq_le_one : t ^ 2 ≤ 1 := by
    have ht_nn : 0 ≤ t := ht_pos.le
    have : t * t ≤ 1 * 1 := mul_le_mul ht_le_one ht_le_one ht_nn (by norm_num)
    linarith [show t ^ 2 = t * t from by ring]
  have ht_six_le_four : t ^ 6 ≤ t ^ 4 := by
    have h_eq : t ^ 6 = t ^ 4 * t ^ 2 := by ring
    have h_t4_nn : 0 ≤ t ^ 4 := by positivity
    have h_mul : t ^ 4 * t ^ 2 ≤ t ^ 4 * 1 := mul_le_mul_of_nonneg_left ht_sq_le_one h_t4_nn
    linarith
  have h_t6_r2_le : t ^ 6 * 𝓢.r ^ 2 / 16 ≤ t ^ 4 * 𝓢.r ^ 2 / 16 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ht_six_le_four hr_sq_nn)
      (by norm_num)
  -- Combine.
  have h_β_v_le_4 : β ^ 2 * ‖v‖ ^ 2 ≤ t ^ 4 * 𝓢.r ^ 2 / 16 :=
    le_trans h_β_v_le h_t6_r2_le
  have h_sum_le : α ^ 2 * 𝓢.r ^ 2 + β ^ 2 * ‖v‖ ^ 2 ≤
      t ^ 4 * 𝓢.r ^ 2 / 4 + t ^ 4 * 𝓢.r ^ 2 / 16 := by
    linarith
  have h_combined : t ^ 4 * 𝓢.r ^ 2 / 4 + t ^ 4 * 𝓢.r ^ 2 / 16 ≤ t ^ 4 * 𝓢.r ^ 2 := by
    have h_t4_r2_nn : 0 ≤ t ^ 4 * 𝓢.r ^ 2 := mul_nonneg (by positivity) hr_sq_nn
    linarith
  have h_total : ‖𝓢.expMap u v - (u + v)‖ ^ 2 ≤ t ^ 4 * 𝓢.r ^ 2 := by
    rw [h_diff, h_norm_sq]
    linarith
  -- Translate t⁴ r² = ‖v‖⁴/r², take square root.
  have h_t4_r2 : t ^ 4 * 𝓢.r ^ 2 = ‖v‖ ^ 4 / 𝓢.r ^ 2 := by
    rw [ht_def]; field_simp
  rw [h_t4_r2] at h_total
  -- ‖expMap u v - (u + v)‖² ≤ ‖v‖⁴/r² = (‖v‖²/r)².
  have h_target_sq : (‖v‖ ^ 2 / 𝓢.r) ^ 2 = ‖v‖ ^ 4 / 𝓢.r ^ 2 := by
    field_simp
  rw [← h_target_sq] at h_total
  have h_target_nn : 0 ≤ ‖v‖ ^ 2 / 𝓢.r :=
    div_nonneg (sq_nonneg _) hr_pos.le
  exact abs_le_of_sq_le_sq' h_total h_target_nn |>.2

/-- **Lemma 5 (Tangentiality).** `T_μ(u) ∈ T_u Sr` for every
`u ∈ Sr ∩ int C`. -/
theorem tangent_T {μ : ℝ} (_hμ : 0 < μ) {u : H X Y}
    (hS : u ∈ 𝓢.sphere) (hC : u ∈ 𝓢.C_interior) :
    inner ℝ u (𝓢.T μ u) = (0 : ℝ) := by
  unfold T
  rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
      𝓢.inner_u_Q (𝓢.C_interior_subset_Cplus hC), 𝓢.inner_u_phi u hC,
      real_inner_self_eq_norm_sq]
  have huu : ‖u‖ ^ 2 = (𝓢.ν : ℝ) + 1 := by
    have hnorm : ‖u‖ = 𝓢.r := hS
    rw [hnorm, 𝓢.r_sq]
  rw [huu]
  ring

/-- **Theorem 8 (A posteriori error bound, ambient form).**
`‖u - u*(μ)‖ ≤ ‖T_μ(u)‖ / μ` for every `u ∈ int C`. -/
theorem error_bound {μ : ℝ} (hμ : 0 < μ) {u : H X Y} (hu : u ∈ 𝓢.C_interior) :
    ‖u - 𝓢.centralPathPoint μ hμ‖ ≤ ‖𝓢.T μ u‖ / μ := by
  set u_star := 𝓢.centralPathPoint μ hμ
  obtain ⟨hC_star, hT_star⟩ := 𝓢.centralPathPoint_isCentralPathPoint μ hμ
  -- Monotonicity of Q on Cplus and φ on C_interior:
  have h_Q : 0 ≤ inner ℝ (u - u_star) (𝓢.Q u - 𝓢.Q u_star) :=
    𝓢.Q_monotone u (𝓢.C_interior_subset_Cplus hu) u_star
      (𝓢.C_interior_subset_Cplus hC_star)
  have h_phi : 0 ≤ inner ℝ (u - u_star) (𝓢.φ u - 𝓢.φ u_star) :=
    𝓢.phi_monotone u hu u_star hC_star
  have h_T_diff : 𝓢.T μ u - 𝓢.T μ u_star =
      (𝓢.Q u - 𝓢.Q u_star) + μ • (u - u_star) + μ • (𝓢.φ u - 𝓢.φ u_star) := by
    unfold T; module
  have h_sm : μ * ‖u - u_star‖ ^ 2 ≤
      inner ℝ (u - u_star) (𝓢.T μ u - 𝓢.T μ u_star) := by
    rw [h_T_diff, inner_add_right, inner_add_right, inner_smul_right,
        inner_smul_right, real_inner_self_eq_norm_sq]
    have h_phi_mul : 0 ≤ μ * inner ℝ (u - u_star) (𝓢.φ u - 𝓢.φ u_star) :=
      mul_nonneg hμ.le h_phi
    linarith
  rw [hT_star, sub_zero] at h_sm
  have h_cs : inner ℝ (u - u_star) (𝓢.T μ u) ≤ ‖u - u_star‖ * ‖𝓢.T μ u‖ :=
    real_inner_le_norm _ _
  have h_combined : μ * ‖u - u_star‖ ^ 2 ≤ ‖u - u_star‖ * ‖𝓢.T μ u‖ :=
    le_trans h_sm h_cs
  by_cases h_eq : u = u_star
  · rw [h_eq, sub_self, norm_zero]
    positivity
  · have h_pos : 0 < ‖u - u_star‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h_eq)
    have key : μ * ‖u - u_star‖ ≤ ‖𝓢.T μ u‖ := by
      have h1 : (μ * ‖u - u_star‖) * ‖u - u_star‖ ≤
          ‖𝓢.T μ u‖ * ‖u - u_star‖ := by
        rw [show (μ * ‖u - u_star‖) * ‖u - u_star‖ = μ * ‖u - u_star‖ ^ 2
              from by ring,
            show ‖𝓢.T μ u‖ * ‖u - u_star‖ = ‖u - u_star‖ * ‖𝓢.T μ u‖
              from mul_comm _ _]
        exact h_combined
      exact le_of_mul_le_mul_right h1 h_pos
    rw [le_div_iff₀ hμ, mul_comm]
    exact key

/-- **Theorem 8 (A posteriori error bound, tangent form).**
On the sphere, the bound sharpens to the tangent-projected residual:
`‖u - u*(μ)‖ ≤ ‖P_u T_μ(u)‖ / μ`. On the sphere `T_μ u` is already
tangent (`tangent_T`), so `P_u T_μ u = T_μ u` and this is just
`error_bound`. -/
theorem error_bound_tangent {μ : ℝ} (hμ : 0 < μ) {u : H X Y}
    (hS : u ∈ 𝓢.sphere) (hC : u ∈ 𝓢.C_interior) :
    ‖u - 𝓢.centralPathPoint μ hμ‖ ≤ ‖proj u (𝓢.T μ u)‖ / μ := by
  rw [proj_of_orthogonal u _ (𝓢.tangent_T hμ hS hC)]
  exact 𝓢.error_bound hμ hC

end IrnSetup

end Irn
