/-
# Sphere geometry, tangentiality, error bound (paper §3)

The sphere `Sr ⊆ H`, the orthogonal projector `P_u` onto the tangent
space, the tangentiality lemma, and the a-posteriori error bound.

Paper references:
* §3.1 (geometry)
* Lemma 6 (tangentiality) → `tangent_T`
* Theorem 7 (a posteriori error bound) → `error_bound`,
  `error_bound_tangent`
-/

import Irn.CentralPath
import Irn.Analytic

namespace Irn

open scoped InnerProductSpace

section Projector

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

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

namespace ProblemData

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  (𝓟 : ProblemData X Y)

/-- The sphere `Sr = { u : ‖u‖ = r }`. -/
def sphere : Set (H X Y) := {u | ‖u‖ = 𝓟.r}

/-- **Lemma 6 (Tangentiality).** `T_μ(u) ∈ T_u Sr` for every
`u ∈ Sr ∩ int C`. -/
theorem tangent_T {μ : ℝ} (_hμ : 0 < μ) {u : H X Y}
    (hS : u ∈ 𝓟.sphere) (hC : u ∈ 𝓟.C_interior) :
    inner ℝ u (𝓟.T μ u) = (0 : ℝ) := by
  unfold T
  rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
      𝓟.inner_u_Q (𝓟.C_interior_subset_Cplus hC), 𝓟.inner_u_phi u hC,
      real_inner_self_eq_norm_sq]
  have huu : ‖u‖ ^ 2 = (𝓟.ν : ℝ) + 1 := by
    have hnorm : ‖u‖ = 𝓟.r := hS
    rw [hnorm, 𝓟.r_sq]
  rw [huu]
  ring

/-- **Theorem 7 (A posteriori error bound, ambient form).**
`‖u - u*(μ)‖ ≤ ‖T_μ(u)‖ / μ` for every `u ∈ int C`. -/
theorem error_bound {μ : ℝ} (hμ : 0 < μ) {u : H X Y} (hu : u ∈ 𝓟.C_interior) :
    ‖u - 𝓟.centralPathPoint μ hμ‖ ≤ ‖𝓟.T μ u‖ / μ := by
  set u_star := 𝓟.centralPathPoint μ hμ
  obtain ⟨hC_star, hT_star⟩ := 𝓟.centralPathPoint_isCentralPathPoint μ hμ
  -- Monotonicity of Q on Cplus and φ on C_interior:
  have h_Q : 0 ≤ inner ℝ (u - u_star) (𝓟.Q u - 𝓟.Q u_star) :=
    𝓟.Q_monotone u (𝓟.C_interior_subset_Cplus hu) u_star
      (𝓟.C_interior_subset_Cplus hC_star)
  have h_phi : 0 ≤ inner ℝ (u - u_star) (𝓟.φ u - 𝓟.φ u_star) :=
    𝓟.phi_monotone u hu u_star hC_star
  have h_T_diff : 𝓟.T μ u - 𝓟.T μ u_star =
      (𝓟.Q u - 𝓟.Q u_star) + μ • (u - u_star) + μ • (𝓟.φ u - 𝓟.φ u_star) := by
    unfold T; module
  have h_sm : μ * ‖u - u_star‖ ^ 2 ≤
      inner ℝ (u - u_star) (𝓟.T μ u - 𝓟.T μ u_star) := by
    rw [h_T_diff, inner_add_right, inner_add_right, inner_smul_right,
        inner_smul_right, real_inner_self_eq_norm_sq]
    have h_phi_mul : 0 ≤ μ * inner ℝ (u - u_star) (𝓟.φ u - 𝓟.φ u_star) :=
      mul_nonneg hμ.le h_phi
    linarith
  rw [hT_star, sub_zero] at h_sm
  have h_cs : inner ℝ (u - u_star) (𝓟.T μ u) ≤ ‖u - u_star‖ * ‖𝓟.T μ u‖ :=
    real_inner_le_norm _ _
  have h_combined : μ * ‖u - u_star‖ ^ 2 ≤ ‖u - u_star‖ * ‖𝓟.T μ u‖ :=
    le_trans h_sm h_cs
  by_cases h_eq : u = u_star
  · rw [h_eq, sub_self, norm_zero]
    positivity
  · have h_pos : 0 < ‖u - u_star‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h_eq)
    have key : μ * ‖u - u_star‖ ≤ ‖𝓟.T μ u‖ := by
      have h1 : (μ * ‖u - u_star‖) * ‖u - u_star‖ ≤
          ‖𝓟.T μ u‖ * ‖u - u_star‖ := by
        rw [show (μ * ‖u - u_star‖) * ‖u - u_star‖ = μ * ‖u - u_star‖ ^ 2
              from by ring,
            show ‖𝓟.T μ u‖ * ‖u - u_star‖ = ‖u - u_star‖ * ‖𝓟.T μ u‖
              from mul_comm _ _]
        exact h_combined
      exact le_of_mul_le_mul_right h1 h_pos
    rw [le_div_iff₀ hμ, mul_comm]
    exact key

/-- **Theorem 7 (A posteriori error bound, tangent form).**
On the sphere, the bound sharpens to the tangent-projected residual:
`‖u - u*(μ)‖ ≤ ‖P_u T_μ(u)‖ / μ`. On the sphere `T_μ u` is already
tangent (`tangent_T`), so `P_u T_μ u = T_μ u` and this is just
`error_bound`. -/
theorem error_bound_tangent {μ : ℝ} (hμ : 0 < μ) {u : H X Y}
    (hS : u ∈ 𝓟.sphere) (hC : u ∈ 𝓟.C_interior) :
    ‖u - 𝓟.centralPathPoint μ hμ‖ ≤ ‖proj u (𝓟.T μ u)‖ / μ := by
  rw [proj_of_orthogonal u _ (𝓟.tangent_T hμ hS hC)]
  exact 𝓟.error_bound hμ hC

/-- The Newton corrector preserves the constraint set: combining
Proposition 11 (well-definedness within a basin) and Theorem 12
(the iterates stay on `Sr ∩ int C`). Built from the two analytic
hypotheses `rjnStep_norm_sq` and `rjnStep_in_C`. -/
theorem rjnStep_invariant
    {μ : ℝ} (hμ : 0 < μ) {u : H X Y} (hS : u ∈ 𝓟.sphere)
    (hC : u ∈ 𝓟.C_interior) :
    𝓟.rjnStep μ u ∈ 𝓟.sphere ∧ 𝓟.rjnStep μ u ∈ 𝓟.C_interior := by
  have h_norm : ‖u‖ = 𝓟.r := hS
  have h_norm_sq : ‖u‖ ^ 2 = (𝓟.ν : ℝ) + 1 := by
    rw [h_norm, 𝓟.r_sq]
  have h_step_norm_sq : ‖𝓟.rjnStep μ u‖ ^ 2 = (𝓟.ν : ℝ) + 1 :=
    𝓟.rjnStep_norm_sq μ u hμ h_norm_sq hC
  refine ⟨?_, 𝓟.rjnStep_in_C μ u hμ h_norm_sq hC⟩
  show ‖𝓟.rjnStep μ u‖ = 𝓟.r
  unfold r
  rw [← Real.sqrt_sq (norm_nonneg _), h_step_norm_sq]

end ProblemData

end Irn
