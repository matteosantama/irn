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

end Projector

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  (𝓢 : IrnSetup H)

/-- The sphere `Sr = { u : ‖u‖ = r }`. -/
def sphere : Set H := {u | ‖u‖ = 𝓢.r}

/-- **Lemma 6 (Tangentiality).** `T_μ(u) ∈ T_u Sr` for every
`u ∈ Sr ∩ int C`. -/
theorem tangent_T {μ : ℝ} (hμ : 0 < μ) {u : H}
    (hS : u ∈ sphere 𝓢) (hC : u ∈ 𝓢.C) :
    inner ℝ u (T 𝓢 μ u) = (0 : ℝ) := by
  unfold T
  rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
      𝓢.inner_u_Q u (𝓢.C_subset_Cplus hC), 𝓢.inner_u_phi u hC,
      real_inner_self_eq_norm_sq]
  have huu : ‖u‖ ^ 2 = (𝓢.ν : ℝ) + 1 := by
    have hnorm : ‖u‖ = 𝓢.r := hS
    rw [hnorm, 𝓢.r_sq]
  rw [huu]
  ring

/-- **Theorem 7 (A posteriori error bound, ambient form).**
`‖u - u*(μ)‖ ≤ ‖T_μ(u)‖ / μ` for every `u ∈ int C`. -/
theorem error_bound {μ : ℝ} (hμ : 0 < μ) {u : H} (hu : u ∈ 𝓢.C) :
    ‖u - centralPathPoint 𝓢 μ hμ‖ ≤ ‖T 𝓢 μ u‖ / μ := sorry

/-- **Theorem 7 (A posteriori error bound, tangent form).**
On the sphere, the bound sharpens to the tangent-projected residual:
`‖u - u*(μ)‖ ≤ ‖P_u T_μ(u)‖ / μ`. -/
theorem error_bound_tangent {μ : ℝ} (hμ : 0 < μ) {u : H}
    (hS : u ∈ sphere 𝓢) (hC : u ∈ 𝓢.C) :
    ‖u - centralPathPoint 𝓢 μ hμ‖ ≤ ‖proj u (T 𝓢 μ u)‖ / μ := sorry

end Irn
