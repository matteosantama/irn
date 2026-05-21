/-
# Sphere geometry, tangentiality, error bound (paper §3, §7.1)

The sphere `Sr ⊆ H`, the orthogonal projector `P_u` onto the tangent
space, the tangentiality lemma, the a-posteriori error bound, and the
closed-form geodesic exponential of `Sr`.

Paper references:
* §3.1 (geometry)
* §3.1 Lemma 5 (tangentiality) → `tangent_T`
* §3.3 Theorem 8 (a posteriori error bound) → `error_bound`,
  `error_bound_tangent`
* §7.1 eq. `eq:exp-map` (geodesic exp) → `expMap`
* §7.1 Proposition 17 (exact sphericity of `exp_u`) → `expMap_mem_sphere`
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

/-- **Proposition 17 (Exact sphericity of `exp_u`).** For `u ∈ Sr` and
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

/-- The Newton corrector preserves the constraint set: combining
Proposition 10 (well-definedness within a basin) and Theorem 11
(the iterates stay on `Sr ∩ int C`). Built from the two analytic
hypotheses `rjnStep_norm_sq` and `rjnStep_in_C`. -/
theorem rjnStep_invariant
    {μ : ℝ} (hμ : 0 < μ) {u : H X Y} (hS : u ∈ 𝓢.sphere)
    (hC : u ∈ 𝓢.C_interior) :
    𝓢.rjnStep μ u ∈ 𝓢.sphere ∧ 𝓢.rjnStep μ u ∈ 𝓢.C_interior := by
  have h_norm : ‖u‖ = 𝓢.r := hS
  have h_norm_sq : ‖u‖ ^ 2 = (𝓢.ν : ℝ) + 1 := by
    rw [h_norm, 𝓢.r_sq]
  have h_step_norm_sq : ‖𝓢.rjnStep μ u‖ ^ 2 = (𝓢.ν : ℝ) + 1 :=
    𝓢.rjnStep_norm_sq μ u hμ h_norm_sq hC
  refine ⟨?_, 𝓢.rjnStep_in_C μ u hμ h_norm_sq hC⟩
  show ‖𝓢.rjnStep μ u‖ = 𝓢.r
  unfold r
  rw [← Real.sqrt_sq (norm_nonneg _), h_step_norm_sq]

end IrnSetup

end Irn
