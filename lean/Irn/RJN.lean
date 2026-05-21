/-
# Riemannian Josephy–Newton on `Sr` (paper §5)

The splitting `T_μ = h + Ψ`, the augmented Newton inclusion with a
Lagrange multiplier for the sphere constraint, existence/uniqueness
of the multiplier (Proposition 10), and local quadratic convergence
(Theorem 11).

**Variant note.** Paper §5.3 introduces three variants of the RJN step:
* **A** — sphericity constraint `C_A(u) = ‖u‖² − (ν+1)`, identity
  retraction.
* **B** — tangency constraint `C_B(u) = u_k⊤u − (ν+1)`, projection
  retraction `r·(u_k+v)/‖u_k+v‖`.
* **C** — tangency constraint `C_B`, geodesic retraction `exp_{u_k}`.

The Lean development currently models only Variant A: the placeholders
`IsRJNStepA` and `IsRJNStepB` are definitionally equal, and `rjnStep` /
`rjnLambda` come from a single sorry-stubbed analytic spec. Adding the
B/C tangent solve plus geodesic exponential is future work.

Paper references:
* §5.1 eq. `eq:splitting`        — splitting `T_μ = h + Ψ`
* §5.3 eq. `eq:rjn`              — Riemannian Josephy–Newton step
* §5.5 Proposition 10 (existence and local uniqueness of `λ_k`)
* §5.6 Theorem 11 (local quadratic convergence of Variants A, B, C)
-/

import Irn.Resolvent

namespace Irn

open scoped InnerProductSpace

namespace IrnSetup

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- The smooth summand `h(u) = μ u + μ ∇F*(u) = μ u + μ (0, ∇f*(y), 0)`. -/
noncomputable def h (𝓢 : IrnSetup X Y) (μ : ℝ) (u : H X Y) : H X Y :=
  μ • u + μ • 𝓢.φ u

/-- Variant A (sphericity, paper §5.3): `(u_next, lam)` is the augmented
Newton step iff `u_next` is the corrector output and `lam` is the
sphere-constraint Lagrange multiplier. Both come from the analytic
sorry'd definitions `rjnStep` and `rjnLambda`. -/
def IsRJNStepA (𝓢 : IrnSetup X Y) (μ : ℝ) (u_k u_next : H X Y) (lam : ℝ) :
    Prop :=
  u_next = 𝓢.rjnStep μ u_k ∧ lam = 𝓢.rjnLambda μ u_k

/-- Variant B (tangency + projection retraction, paper §5.3). Identified
here with Variant A as a placeholder until the tangent solve / projection
retraction is formalised separately. -/
def IsRJNStepB (𝓢 : IrnSetup X Y) (μ : ℝ) (u_k u_next : H X Y) (lam : ℝ) :
    Prop :=
  IsRJNStepA 𝓢 μ u_k u_next lam

variable (𝓢 : IrnSetup X Y)

/-- **Proposition 10 (Existence and local uniqueness of `λ_k`).** -/
theorem lambda_exists_unique
    {μ : ℝ} (hμ : 0 < μ) :
    ∃ U : Set (H X Y), ∃ Λ : Set ℝ,
      (𝓢.centralPathPoint μ hμ ∈ U) ∧ ((0 : ℝ) ∈ Λ) ∧
      IsOpen U ∧ IsOpen Λ ∧
      ∀ u_k ∈ U, u_k ∈ 𝓢.sphere →
        ∃! lam : ℝ, lam ∈ Λ ∧
          ∃ u_next : H X Y, IsRJNStepA 𝓢 μ u_k u_next lam := by
  set u_star := 𝓢.centralPathPoint μ hμ
  obtain ⟨hC_star, hT_star⟩ := 𝓢.centralPathPoint_isCentralPathPoint μ hμ
  have h_T : 𝓢.Q u_star + μ • u_star + μ • 𝓢.φ u_star = 0 := by
    have := hT_star; unfold T at this; exact this
  have h_lam_zero : 𝓢.rjnLambda μ u_star = 0 :=
    𝓢.rjnLambda_at_central μ u_star hμ hC_star h_T
  have h_cont : ContinuousAt (𝓢.rjnLambda μ) u_star :=
    𝓢.rjnLambda_continuousAt_central μ u_star hμ hC_star h_T
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

/-- **Theorem 11 (Local quadratic convergence).** Currently states the
result only for Variant A (via `rjnStep`); Variants B and C from
paper §5.6 are future work. -/
theorem rjn_quadratic_convergence
    {μ : ℝ} (hμ : 0 < μ) :
    ∃ U : Set (H X Y), IsOpen U ∧ 𝓢.centralPathPoint μ hμ ∈ U ∧
      ∀ u₀ ∈ U, u₀ ∈ 𝓢.sphere → u₀ ∈ 𝓢.C_interior →
        ∃ seq : ℕ → H X Y,
          seq 0 = u₀ ∧
          (∀ k, seq k ∈ 𝓢.sphere ∩ 𝓢.C_interior) ∧
          ∃ C : ℝ, 0 < C ∧
            ∀ k, ‖seq (k+1) - 𝓢.centralPathPoint μ hμ‖ ≤
                   C * ‖seq k - 𝓢.centralPathPoint μ hμ‖ ^ 2 := by
  set u_star := 𝓢.centralPathPoint μ hμ
  obtain ⟨hC_star, hT_star⟩ := 𝓢.centralPathPoint_isCentralPathPoint μ hμ
  have h_T : 𝓢.Q u_star + μ • u_star + μ • 𝓢.φ u_star = 0 := by
    have := hT_star; unfold T at this; exact this
  obtain ⟨U, hU_open, hU_mem, K, hK_pos, h_basin, h_contract⟩ :=
    𝓢.rjnStep_euclidean_basin μ hμ u_star hC_star h_T
  refine ⟨U, hU_open, hU_mem, ?_⟩
  intros u₀ hu₀_U hu₀_sphere hu₀_C
  let seq_fn : ℕ → H X Y := fun k =>
    Nat.rec u₀ (fun _ s => 𝓢.rjnStep μ s) k
  have h_seq_succ : ∀ k, seq_fn (k+1) = 𝓢.rjnStep μ (seq_fn k) := fun _ => rfl
  have h_strong : ∀ k,
      seq_fn k ∈ U ∧ seq_fn k ∈ 𝓢.sphere ∧ seq_fn k ∈ 𝓢.C_interior := by
    intro k
    induction k with
    | zero => exact ⟨hu₀_U, hu₀_sphere, hu₀_C⟩
    | succ k ih =>
      obtain ⟨h_U_k, h_sphere_k, h_C_k⟩ := ih
      have h_norm_sq : ‖seq_fn k‖ ^ 2 = (𝓢.ν : ℝ) + 1 := by
        have hn : ‖seq_fn k‖ = 𝓢.r := h_sphere_k
        rw [hn, 𝓢.r_sq]
      have h_inv := 𝓢.rjnStep_invariant hμ h_sphere_k h_C_k
      refine ⟨?_, h_inv.1, h_inv.2⟩
      rw [h_seq_succ]
      exact h_basin (seq_fn k) h_U_k h_norm_sq h_C_k
  refine ⟨seq_fn, rfl, ?_, K, hK_pos, ?_⟩
  · intro k
    exact ⟨(h_strong k).2.1, (h_strong k).2.2⟩
  · intro k
    obtain ⟨h_U_k, h_sphere_k, h_C_k⟩ := h_strong k
    have h_norm_sq : ‖seq_fn k‖ ^ 2 = (𝓢.ν : ℝ) + 1 := by
      have hn : ‖seq_fn k‖ = 𝓢.r := h_sphere_k
      rw [hn, 𝓢.r_sq]
    rw [h_seq_succ]
    exact h_contract (seq_fn k) h_U_k h_norm_sq h_C_k

end IrnSetup

end Irn
