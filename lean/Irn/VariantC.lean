/-
# Variant C of the Riemannian Josephy–Newton step (paper §5.3, §5.6)

Variant C of paper §5.3 combines the **tangency constraint** `C_B(u) =
u_k⊤ u − (ν+1) = 0` with the **closed-form geodesic retraction**
`exp_{u_k}` (paper eq. `eq:exp-map`):

  `u_{k+1}^♯  ←  tangent inclusion solve at level μ`
  `u_{k+1}    ←  exp_{u_k}(u_{k+1}^♯ − u_k)`.

This file isolates Variant C: it states the Newton direction as a
sorry-stubbed analytic primitive (`rjnDirectionC`), assembles the step
via the proven `expMap`, derives sphericity of the iterates from
`expMap_mem_sphere` + tangency, and states the local quadratic
convergence theorem (Theorem 11 specialised to Variant C).

The remaining sorries flag the analytic content that the paper proof
imports from Riemannian Newton-Kantorovich theory
(\\cite[\\S6.3]{absil2008manifolds}) plus the set-valued
Josephy–Newton extension of \\cite[\\S3]{bonnans1994local}, neither of
which is in Mathlib at the time of writing.

Paper references:
* §5.3 (Riemannian Josephy–Newton step — variant C row of the variants
  table) → `rjnStepC`
* §5.3 eq. `eq:variantC-incl` (tangent inclusion) → `rjnDirectionC`,
  `rjnDirectionC_tangent`
* §5.6 Theorem 11 (Local quadratic convergence) → `rjnStepC_quadratic_basin`
  (basin form) and `rjnStepC_quadratic_convergence` (sequence form)
* §7.1 Proposition 17 (exact sphericity of `exp_u`) →
  `expMap_mem_sphere` (used inside `rjnStepC_mem_sphere`)
-/

import Irn.Sphere

namespace Irn
namespace IrnSetup

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
variable (𝓢 : IrnSetup X Y)

open scoped InnerProductSpace

/-! ### The Newton direction (paper §5.3 eq. `eq:variantC-incl`)

The Variant C tangent inclusion at `u_k ∈ Sr ∩ int C`, level `μ > 0`,
asks for a pair `(v_k, λ_k) ∈ T_{u_k}Sr × ℝ` satisfying

  `0 ∈ h(u_k) + H_k v_k + Ψ(u_k + v_k) + λ_k u_k`,    `u_k⊤ v_k = 0`,

with `H_k = μ I + μ ∇²F*(u_k)`. By Proposition 10
(`Irn.RJN.lambda_exists_unique` placeholder), the system admits a
unique solution in a neighbourhood of the central-path point. -/

/-- The Variant C Newton direction `v_k = u_{k+1}^♯ − u_k`. Sorry-stub:
the paper definition is the tangent component of the Variant C
inclusion solve at `(u_k, μ)`. -/
noncomputable def rjnDirectionC (_ : IrnSetup X Y) (_ : ℝ) (_ : H X Y) :
    H X Y := sorry

/-- The Variant C direction lies in `T_{u_k}Sr`: `⟨u_k, v_k⟩ = 0`. This
is the tangency constraint `C_B(u_k + v_k) = 0` rewritten using
`‖u_k‖² = ν + 1`. Sorry-stub. -/
theorem rjnDirectionC_tangent (𝓢 : IrnSetup X Y) (μ : ℝ) (u_k : H X Y) :
    inner ℝ u_k (𝓢.rjnDirectionC μ u_k) = (0 : ℝ) := sorry

/-! ### The Variant C step -/

/-- **Variant C step.** Take the tangent Newton direction and
exponentiate it along the geodesic of `Sr`:
`u_{k+1} := exp_{u_k}(rjnDirectionC μ u_k)`. -/
noncomputable def rjnStepC (μ : ℝ) (u_k : H X Y) : H X Y :=
  𝓢.expMap u_k (𝓢.rjnDirectionC μ u_k)

/-- **Sphericity of the Variant C iterate.** Combines tangency of the
Newton direction (`rjnDirectionC_tangent`) with the exact-sphere
property of `exp_u` (`expMap_mem_sphere`, paper Proposition 17). -/
theorem rjnStepC_mem_sphere {μ : ℝ} {u_k : H X Y} (hu_k : u_k ∈ 𝓢.sphere) :
    𝓢.rjnStepC μ u_k ∈ 𝓢.sphere :=
  𝓢.expMap_mem_sphere u_k _ hu_k (𝓢.rjnDirectionC_tangent μ u_k)

/-- **Interior preservation for Variant C** (sorry — basin-dependent).
For `u_k` in a neighbourhood of the central-path point, the Newton step
stays in `int C`. The paper proof relies on the basin from
Newton–Kantorovich (Lemma 15) plus continuity of `exp` and the cone
membership of the central-path point. -/
theorem rjnStepC_in_C {μ : ℝ} (hμ : 0 < μ) {u_k : H X Y}
    (hu_k_S : u_k ∈ 𝓢.sphere) (hu_k_C : u_k ∈ 𝓢.C_interior) :
    𝓢.rjnStepC μ u_k ∈ 𝓢.C_interior := sorry

/-! ### Quadratic contraction basin

The analytic core of Theorem 11 for Variant C. Existence of an open
basin in which one Variant C step contracts the distance to `u*(μ)`
quadratically.

**Paper proof sketch (Step 2 of `thm:quadratic`).** Variants B and C
share the same tangent inclusion (paper eq. `eq:variantC-incl`) and
therefore the same Newton direction `v_k ∈ T_{u_k}Sr`; they differ only
in how `v_k` is retracted to `Sr`. The projection retraction
`R̃_{u_k}` (Variant B) and the geodesic retraction `exp_{u_k}` (Variant
C) are both second-order retractions of `Sr` in the sense of
\\cite[Def.~4.1.1]{absil2008manifolds}, so the Riemannian Newton
convergence theorem \\cite[Thm.~6.3.2]{absil2008manifolds} applies
verbatim to both. The retraction discrepancy
`‖R̃_{u_k}(v_k) − exp_{u_k}(v_k)‖ = O(‖v_k‖³)` (paper
eq. `eq:retraction-discrepancy`) is dominated by the `O(‖v_k‖²) =
O(‖u_k − u*(μ)‖²)` Variant B bound, leaving the quadratic rate
unchanged.

The full proof requires (i) the set-valued Josephy–Newton convergence
theorem \\cite[Thm.~3.1]{bonnans1994local}, (ii) Mathlib-level
Riemannian Newton on embedded submanifolds, (iii) the LHSCB
self-concordant Lipschitz bound — none currently in Mathlib. -/
theorem rjnStepC_quadratic_basin {μ : ℝ} (hμ : 0 < μ) :
    ∃ U : Set (H X Y), IsOpen U ∧ 𝓢.centralPathPoint μ hμ ∈ U ∧
      ∃ K : ℝ, 0 < K ∧
        (∀ u ∈ U, u ∈ 𝓢.sphere → u ∈ 𝓢.C_interior →
          𝓢.rjnStepC μ u ∈ U) ∧
        (∀ u ∈ U, u ∈ 𝓢.sphere → u ∈ 𝓢.C_interior →
          ‖𝓢.rjnStepC μ u - 𝓢.centralPathPoint μ hμ‖ ≤
            K * ‖u - 𝓢.centralPathPoint μ hμ‖ ^ 2) := sorry

/-! ### Theorem 11 (Variant C): local quadratic convergence -/

/-- **Theorem 11 specialised to Variant C** (paper §5.6).

Assume `f ∈ C³(int K)` (encoded as `𝓢.d ≥ 3`, automatic). For each
`μ > 0` there is an open neighbourhood `U` of `u*(μ)` in `H` and a
constant `K > 0` such that, starting from any `u₀ ∈ U ∩ Sr ∩ int C`,
the iterates
  `u_{k+1} := rjnStepC μ u_k`
stay in `Sr ∩ int C` and satisfy
  `‖u_{k+1} − u*(μ)‖ ≤ K · ‖u_k − u*(μ)‖²`.

This packages the basin theorem `rjnStepC_quadratic_basin` together
with the invariants `rjnStepC_mem_sphere` (proven from `expMap_mem_sphere`
and tangency) and `rjnStepC_in_C` into a recursive sequence. -/
theorem rjnStepC_quadratic_convergence {μ : ℝ} (hμ : 0 < μ) :
    ∃ U : Set (H X Y), IsOpen U ∧ 𝓢.centralPathPoint μ hμ ∈ U ∧
      ∀ u₀ ∈ U, u₀ ∈ 𝓢.sphere → u₀ ∈ 𝓢.C_interior →
        ∃ seq : ℕ → H X Y,
          seq 0 = u₀ ∧
          (∀ k, seq k ∈ 𝓢.sphere ∩ 𝓢.C_interior) ∧
          ∃ K : ℝ, 0 < K ∧
            ∀ k, ‖seq (k+1) - 𝓢.centralPathPoint μ hμ‖ ≤
                   K * ‖seq k - 𝓢.centralPathPoint μ hμ‖ ^ 2 := by
  obtain ⟨U, hU_open, hU_mem, K, hK_pos, h_basin, h_contract⟩ :=
    𝓢.rjnStepC_quadratic_basin hμ
  refine ⟨U, hU_open, hU_mem, ?_⟩
  intros u₀ hu₀_U hu₀_S hu₀_C
  let seq_fn : ℕ → H X Y := fun k =>
    Nat.rec u₀ (fun _ s => 𝓢.rjnStepC μ s) k
  have h_seq_succ : ∀ k, seq_fn (k + 1) = 𝓢.rjnStepC μ (seq_fn k) := fun _ => rfl
  have h_strong : ∀ k,
      seq_fn k ∈ U ∧ seq_fn k ∈ 𝓢.sphere ∧ seq_fn k ∈ 𝓢.C_interior := by
    intro k
    induction k with
    | zero => exact ⟨hu₀_U, hu₀_S, hu₀_C⟩
    | succ k ih =>
      obtain ⟨h_U_k, h_S_k, h_C_k⟩ := ih
      refine ⟨?_, ?_, ?_⟩
      · rw [h_seq_succ]; exact h_basin _ h_U_k h_S_k h_C_k
      · rw [h_seq_succ]; exact 𝓢.rjnStepC_mem_sphere h_S_k
      · rw [h_seq_succ]; exact 𝓢.rjnStepC_in_C hμ h_S_k h_C_k
  refine ⟨seq_fn, rfl, ?_, K, hK_pos, ?_⟩
  · intro k; exact ⟨(h_strong k).2.1, (h_strong k).2.2⟩
  · intro k
    obtain ⟨h_U_k, h_S_k, h_C_k⟩ := h_strong k
    rw [h_seq_succ]
    exact h_contract _ h_U_k h_S_k h_C_k

end IrnSetup
end Irn
