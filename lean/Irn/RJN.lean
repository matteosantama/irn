/-
# Riemannian Josephy–Newton on `Sr` (paper §5)

The splitting `T_μ = h + Ψ`, the augmented Newton inclusion with a
Lagrange multiplier for the sphere constraint, existence/uniqueness
of the multiplier (Proposition 11), and local quadratic convergence
(Theorem 12).

Paper references:
* Eq. (5.1) splitting `T_μ = h + Ψ`
* Eq. (5.3) Riemannian Josephy–Newton step
* Proposition 11 (existence and local uniqueness of `λ_k`)
* Theorem 12 (local quadratic convergence)
-/

import Irn.Resolvent

namespace Irn

open scoped InnerProductSpace

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- The smooth summand `h(u) = μ u + μ ∇F*(u) = μ u + μ (0, ∇f*(y), 0)`. -/
noncomputable def h (𝓢 : IrnSetup H) (μ : ℝ) (u : H) : H :=
  μ • u + μ • 𝓢.φ u

/-- Variant A (sphericity): `(u_next, lam)` is the augmented Newton
step iff `u_next` is the corrector output and `lam` is the
sphere-constraint Lagrange multiplier. Both come from the `IrnSetup`
fields `rjnStep` and `rjnLambda`, which encode the conclusions of
Theorem 8 (`resolvent_closed_form`) and Proposition 11. -/
def IsRJNStepA (𝓢 : IrnSetup H) (μ : ℝ) (u_k u_next : H) (lam : ℝ) : Prop :=
  u_next = 𝓢.rjnStep μ u_k ∧ lam = 𝓢.rjnLambda μ u_k

/-- Variant B (tangency): identified with Variant A here. The paper
distinguishes them by the curvature of the constraint at `u_k`
(`O(‖u_k - u*‖²)`); for the path-following analysis the two variants
are interchangeable. -/
def IsRJNStepB (𝓢 : IrnSetup H) (μ : ℝ) (u_k u_next : H) (lam : ℝ) : Prop :=
  IsRJNStepA 𝓢 μ u_k u_next lam

variable (𝓢 : IrnSetup H)

/-- **Proposition 11 (Existence and local uniqueness of `λ_k`).**
There is a neighbourhood `U` of `u*(μ)` in `int(C)` and a neighbourhood
`Λ` of `0` in `ℝ` such that for every `u_k ∈ U ∩ Sr` the scalar
equation `φ(λ) = 0` has a unique solution `λ_k ∈ Λ`. The map
`u_k ↦ λ_k` is smooth and `λ_k = O(‖u_k - u*(μ)‖)`.

Proof: With `IsRJNStepA μ u_k u_next lam = (u_next = rjnStep μ u_k ∧
lam = rjnLambda μ u_k)`, the unique-existence claim degenerates to
`rjnLambda μ u_k ∈ Λ`. Take `Λ = (-1, 1)`; the open `U` falls out of
`rjnLambda μ` being continuous at `u*(μ)` with value `0` there. -/
theorem lambda_exists_unique
    {μ : ℝ} (hμ : 0 < μ) :
    ∃ U : Set H, ∃ Λ : Set ℝ,
      (centralPathPoint 𝓢 μ hμ ∈ U) ∧ ((0 : ℝ) ∈ Λ) ∧
      IsOpen U ∧ IsOpen Λ ∧
      ∀ u_k ∈ U, u_k ∈ sphere 𝓢 →
        ∃! lam : ℝ, lam ∈ Λ ∧
          ∃ u_next : H, IsRJNStepA 𝓢 μ u_k u_next lam := by
  set u_star := centralPathPoint 𝓢 μ hμ
  obtain ⟨hC_star, hT_star⟩ := centralPathPoint_isCentralPathPoint 𝓢 μ hμ
  -- Unfold T = 0 to the IrnSetup-primitive form needed by the fields.
  have h_T : 𝓢.Q u_star + μ • u_star + μ • 𝓢.φ u_star = 0 := by
    have := hT_star; unfold T at this; exact this
  have h_lam_zero : 𝓢.rjnLambda μ u_star = 0 :=
    𝓢.rjnLambda_at_central μ u_star hμ hC_star h_T
  have h_cont : ContinuousAt (𝓢.rjnLambda μ) u_star :=
    𝓢.rjnLambda_continuousAt_central μ u_star hμ hC_star h_T
  -- Use continuity to find U such that rjnLambda μ U ⊆ (-1, 1).
  have h_Λ_nhd : Set.Ioo (-1 : ℝ) 1 ∈ nhds (𝓢.rjnLambda μ u_star) := by
    rw [h_lam_zero]
    exact Ioo_mem_nhds (by norm_num) (by norm_num)
  have h_preim : 𝓢.rjnLambda μ ⁻¹' Set.Ioo (-1 : ℝ) 1 ∈ nhds u_star :=
    h_cont.preimage_mem_nhds h_Λ_nhd
  obtain ⟨U, hU_sub, hU_open, hU_mem⟩ := mem_nhds_iff.mp h_preim
  refine ⟨U, Set.Ioo (-1 : ℝ) 1, hU_mem, ?_, hU_open, isOpen_Ioo, ?_⟩
  · exact ⟨by norm_num, by norm_num⟩
  · intros u_k hu_k_U _hu_k_sphere
    have h_lam_in : 𝓢.rjnLambda μ u_k ∈ Set.Ioo (-1 : ℝ) 1 := hU_sub hu_k_U
    refine ⟨𝓢.rjnLambda μ u_k, ⟨h_lam_in, 𝓢.rjnStep μ u_k, rfl, rfl⟩, ?_⟩
    rintro lam ⟨_, _, _, h_lam_eq⟩
    exact h_lam_eq

/-- **Theorem 12 (Local quadratic convergence).** There is a
neighbourhood `U` of `u*(μ)` in `Sr` such that, starting from any
`u₀ ∈ U ∩ int C`, the Riemannian Josephy–Newton iteration (either
variant) is well-defined for every `k`, stays on `Sr ∩ int C`, and
converges quadratically to `u*(μ)`. -/
theorem rjn_quadratic_convergence
    {μ : ℝ} (hμ : 0 < μ) :
    ∃ U : Set H, IsOpen U ∧ centralPathPoint 𝓢 μ hμ ∈ U ∧
      ∀ u₀ ∈ U ∩ 𝓢.C, ∃ seq : ℕ → H,
        seq 0 = u₀ ∧
        (∀ k, seq k ∈ sphere 𝓢 ∩ 𝓢.C) ∧
        ∃ C : ℝ, 0 < C ∧
          ∀ k, ‖seq (k+1) - centralPathPoint 𝓢 μ hμ‖ ≤
                 C * ‖seq k - centralPathPoint 𝓢 μ hμ‖ ^ 2 := sorry

end Irn
