/-
# Variant C of the Riemannian Josephy–Newton step (paper §5.3, §5.6)

Variant C of paper §5.3 combines the **tangency constraint** `C_B(u) =
u_k⊤ u − (ν+1) = 0` with the **closed-form geodesic retraction**
`exp_{u_k}` (paper eq. `eq:exp-map`):

  `u_{k+1}^♯  ←  tangent inclusion solve at level μ`
  `u_{k+1}    ←  exp_{u_k}(u_{k+1}^♯ − u_k)`.

This file isolates Variant C: it defines the Newton direction as
`Classical.choose` over an `IsVariantCSolution` existence predicate
(with `0` as fallback when no solution exists), assembles the step
via the proven `expMap`, derives sphericity of the iterates from
`expMap_mem_sphere` + tangency, and states the local quadratic
convergence theorem (Theorem 11 specialised to Variant C).

The existence branch is provably populated at `u_k = u*(μ)` (via
`IsVariantCSolution_zero_at_centralPath`, with witness `v = 0`); the
extension to a full neighbourhood of `u*(μ)` is paper Proposition 10
and would require implicit-function-theorem analysis of the scalar
`λ`-quadratic of paper §5.5 — present beyond the central-path point
only through the `Classical.choose`/fallback mechanism.

The single remaining sorry is `rjnStepC_quadratic_basin`, the deep
analytic content of paper Theorem 11 (Riemannian Newton-Kantorovich
via \\cite[\\S6.3]{absil2008manifolds} plus set-valued Josephy–Newton
of \\cite[\\S3]{bonnans1994local}, neither in Mathlib at time of
writing).

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
asks for a pair `(v_k, λ_k) ∈ T_{u_k}Sr × ℝ` and a scalar `θ_k > 0`
such that, on the smooth part of `Ψ`,

  `(H_k + M)(u_k + v_k) = H_k u_k − h(u_k) − λ_k u_k + θ_k e_τ`,
  `θ_k · τ(u_k + v_k) = Pₓ(u_k + v_k, u_k + v_k) + μ`,
  `u_k⊤ v_k = 0`,
  `u_k + v_k ∈ C_+`,

with `H_k = μ I + μ ∇²F*(u_k)` and `h(u_k) = μ u_k + μ ∇F*(u_k)`. The
first two lines are the resolvent computation at the `λ`-shifted input
`z(λ_k) = u_k − H_k⁻¹(h(u_k) + λ_k u_k)` (paper §5.4); the third is
the Variant C tangency constraint `C_B(u_k + v_k) = 0` rewritten using
`‖u_k‖² = ν + 1`. -/

/-- **`IsVariantCSolution μ u_k v`** — the property that `v` is the
Variant C tangent-inclusion solution at `(μ, u_k)`. Packages tangency,
cone membership of `u_k + v`, and existence of compatible scalars
`(λ, θ)` satisfying the resolvent equations of paper §5.4. -/
def IsVariantCSolution (𝓢 : IrnSetup X Y) (μ : ℝ) (u_k v : H X Y) : Prop :=
  inner ℝ u_k v = (0 : ℝ) ∧
  (u_k + v) ∈ 𝓢.Cplus ∧
  ∃ θ : ℝ, 0 < θ ∧ ∃ lam : ℝ,
    (𝓢.hessian_h μ u_k + 𝓢.M_clm) (u_k + v) =
      𝓢.hessian_h μ u_k u_k -
        (μ • u_k + μ • 𝓢.f_lhscb.grad u_k + lam • u_k) +
        θ • 𝓢.e_τ ∧
    θ * 𝓢.tau_proj (u_k + v) =
      𝓢.Px_bilinform_clm (u_k + v) (u_k + v) + μ

/-- **The trivial Variant C solution at the central-path point.** At
`u_k = u*(μ)` the fixed-point property `T_μ(u_k) = 0` forces `v_k = 0`,
`λ_k = 0`, `θ_k = (Pₓ(u_k, u_k) + μ) / τ(u_k)`. Concretely:
* tangency `⟨u_k, 0⟩ = 0` is trivial;
* `u_k + 0 = u_k ∈ C_+` from `u_k ∈ int C`;
* the Newton equation reduces to `M u_k + h(u_k) = θ_k e_τ`, which
  follows from `T_μ(u_k) = Q(u_k) + h(u_k) - (μ/τ) e_τ = 0` plus
  `Q(u_k) = M u_k - (Pₓ/τ) e_τ`;
* the scalar equation `θ_k · τ(u_k) = Pₓ(u_k, u_k) + μ` is the
  definition of `θ_k`. -/
theorem IsVariantCSolution_zero_at_centralPath (𝓢 : IrnSetup X Y) {μ : ℝ}
    (hμ : 0 < μ) :
    𝓢.IsVariantCSolution μ (𝓢.centralPathPoint μ hμ) 0 := by
  set u_k := 𝓢.centralPathPoint μ hμ with hu_k_def
  obtain ⟨hC, hT⟩ := 𝓢.centralPathPoint_isCentralPathPoint μ hμ
  have hCplus : u_k ∈ 𝓢.Cplus := 𝓢.C_interior_subset_Cplus hC
  have hτ_pos : 0 < 𝓢.tau_proj u_k := 𝓢.tau_proj_pos hCplus
  have hτ_ne : 𝓢.tau_proj u_k ≠ 0 := ne_of_gt hτ_pos
  have hPx_clm_apply : 𝓢.Px_bilinform_clm u_k u_k =
      𝓢.Px_bilinform (𝓢.x_proj u_k) (𝓢.x_proj u_k) := rfl
  have hPx_nn : 0 ≤ 𝓢.Px_bilinform_clm u_k u_k := by
    rw [hPx_clm_apply]; exact 𝓢.Px_bilinform_self_nonneg _
  set θ : ℝ := (𝓢.Px_bilinform_clm u_k u_k + μ) / 𝓢.tau_proj u_k with hθ_def
  have hθ_pos : 0 < θ := div_pos (by linarith) hτ_pos
  refine ⟨inner_zero_right _, by simpa using hCplus, θ, hθ_pos, 0, ?_, ?_⟩
  · -- Newton equation:
    -- (H_k + M_clm)(u_k + 0) = H_k u_k − (μ•u_k + μ•∇F*(u_k) + 0•u_k) + θ•e_τ
    show (𝓢.hessian_h μ u_k + 𝓢.M_clm) (u_k + 0) =
      𝓢.hessian_h μ u_k u_k -
        (μ • u_k + μ • 𝓢.f_lhscb.grad u_k + (0 : ℝ) • u_k) +
        θ • 𝓢.e_τ
    rw [add_zero, zero_smul, add_zero, ContinuousLinearMap.add_apply]
    -- Reduce: M_clm u_k = θ•e_τ − μ•u_k − μ•∇F*(u_k).
    have h_Q : 𝓢.Q u_k =
        𝓢.M_clm u_k - (𝓢.Px_bilinform_clm u_k u_k / 𝓢.tau_proj u_k) • 𝓢.e_τ := by
      show 𝓢.M_apply u_k - _ • _ = 𝓢.M_clm u_k - _ • _
      rw [show 𝓢.M_apply u_k = 𝓢.M_clm u_k from rfl, hPx_clm_apply]
    have h_φ : 𝓢.φ u_k = 𝓢.f_lhscb.grad u_k + (-1 / 𝓢.tau_proj u_k) • 𝓢.e_τ := rfl
    have h_T_unfolded : 𝓢.Q u_k + μ • u_k + μ • 𝓢.φ u_k = 0 := hT
    rw [h_Q, h_φ] at h_T_unfolded
    -- h_T_unfolded :
    --   (M_clm u_k - (Px/τ)•e_τ) + μ•u_k + μ•(f_lhscb.grad u_k + (-1/τ)•e_τ) = 0
    -- The θ•e_τ coefficient combines: -(Px/τ) - μ·(-1/τ) = -(Px+μ)/τ = -θ.
    have h_coef : (-(𝓢.Px_bilinform_clm u_k u_k / 𝓢.tau_proj u_k))
                  + μ * (-1 / 𝓢.tau_proj u_k) = -θ := by
      rw [hθ_def]; field_simp; ring
    have h_T_rearranged :
        𝓢.M_clm u_k + μ • u_k + μ • 𝓢.f_lhscb.grad u_k = θ • 𝓢.e_τ := by
      have h := h_T_unfolded
      -- h : (M_clm u_k - (Px/τ)•e_τ) + μ•u_k
      --     + μ•(f_lhscb.grad u_k + (-1/τ)•e_τ) = 0
      have heq :
          𝓢.M_clm u_k - (𝓢.Px_bilinform_clm u_k u_k / 𝓢.tau_proj u_k) • 𝓢.e_τ
            + μ • u_k +
            μ • (𝓢.f_lhscb.grad u_k + (-1 / 𝓢.tau_proj u_k) • 𝓢.e_τ) =
          𝓢.M_clm u_k + μ • u_k + μ • 𝓢.f_lhscb.grad u_k +
            ((-(𝓢.Px_bilinform_clm u_k u_k / 𝓢.tau_proj u_k))
                + μ * (-1 / 𝓢.tau_proj u_k)) • 𝓢.e_τ := by
        rw [smul_add, smul_smul]
        module
      rw [heq, h_coef] at h
      -- h : M_clm u_k + μ•u_k + μ•f_lhscb.grad u_k + (-θ)•e_τ = 0
      have h_neg : 𝓢.M_clm u_k + μ • u_k + μ • 𝓢.f_lhscb.grad u_k =
          -((-θ) • 𝓢.e_τ) := eq_neg_of_add_eq_zero_left h
      rw [h_neg, neg_smul, neg_neg]
    -- Goal: H_k u_k + M_clm u_k = H_k u_k - (μ•u_k + μ•f_lhscb.grad u_k) + θ•e_τ
    have h_M : 𝓢.M_clm u_k = θ • 𝓢.e_τ - (μ • u_k + μ • 𝓢.f_lhscb.grad u_k) := by
      rw [eq_sub_iff_add_eq, ← add_assoc]
      exact h_T_rearranged
    rw [h_M]; abel
  · -- Scalar equation: θ · τ(u_k) = Pₓ(u_k, u_k) + μ.
    show θ * 𝓢.tau_proj (u_k + 0) = 𝓢.Px_bilinform_clm (u_k + 0) (u_k + 0) + μ
    rw [add_zero]
    show ((𝓢.Px_bilinform_clm u_k u_k + μ) / 𝓢.tau_proj u_k) *
        𝓢.tau_proj u_k = 𝓢.Px_bilinform_clm u_k u_k + μ
    field_simp

/-- **The Variant C Newton direction.** Constructive total function:
returns the (Classical-choose-extracted) `v` satisfying
`IsVariantCSolution` when one exists; otherwise falls back to `0`. The
existence branch covers at least `u_k = u*(μ)` (via
`IsVariantCSolution_zero_at_centralPath`, with `v = 0` as witness); the
extension to a full neighbourhood of `u*(μ)` is paper Proposition 10
(requires IFT on the scalar `λ`-quadratic, not yet in Mathlib). -/
noncomputable def rjnDirectionC (𝓢 : IrnSetup X Y) (μ : ℝ) (u_k : H X Y) :
    H X Y :=
  haveI : Decidable (∃ v, 𝓢.IsVariantCSolution μ u_k v) := Classical.dec _
  if h : ∃ v, 𝓢.IsVariantCSolution μ u_k v then Classical.choose h else 0

/-- `rjnDirectionC` either satisfies `IsVariantCSolution` (when a
solution exists) or is `0` (fallback). Useful structural disjunction. -/
theorem rjnDirectionC_isVariantCSolution_or_zero (𝓢 : IrnSetup X Y)
    (μ : ℝ) (u_k : H X Y) :
    𝓢.IsVariantCSolution μ u_k (𝓢.rjnDirectionC μ u_k) ∨
      𝓢.rjnDirectionC μ u_k = 0 := by
  unfold rjnDirectionC
  split_ifs with h
  · exact Or.inl (Classical.choose_spec h)
  · exact Or.inr rfl

/-- At the central-path point `u*(μ)`, `rjnDirectionC` satisfies
`IsVariantCSolution` — i.e., it lands in the existence branch.
Follows from `IsVariantCSolution_zero_at_centralPath`, which provides
the witness. -/
theorem rjnDirectionC_isVariantCSolution_at_centralPath (𝓢 : IrnSetup X Y)
    {μ : ℝ} (hμ : 0 < μ) :
    𝓢.IsVariantCSolution μ (𝓢.centralPathPoint μ hμ)
      (𝓢.rjnDirectionC μ (𝓢.centralPathPoint μ hμ)) := by
  unfold rjnDirectionC
  have h : ∃ v, 𝓢.IsVariantCSolution μ (𝓢.centralPathPoint μ hμ) v :=
    ⟨0, 𝓢.IsVariantCSolution_zero_at_centralPath hμ⟩
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- **Tangency of the Variant C direction**: `⟨u_k, v_k⟩ = 0`.
Proven unconditionally by case-splitting on whether `IsVariantCSolution`
holds — in the existence branch tangency comes from the first conjunct
of the predicate, in the fallback branch `v_k = 0` is trivially tangent. -/
theorem rjnDirectionC_tangent (𝓢 : IrnSetup X Y) (μ : ℝ) (u_k : H X Y) :
    inner ℝ u_k (𝓢.rjnDirectionC μ u_k) = (0 : ℝ) := by
  rcases 𝓢.rjnDirectionC_isVariantCSolution_or_zero μ u_k with h | h
  · exact h.1
  · rw [h]; exact inner_zero_right _

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

/-! ### Quadratic contraction basin

The analytic core of Theorem 11 for Variant C. Existence of an open
basin `U ⊆ C_interior` around `u*(μ)` such that one Variant C step
maps `U ∩ Sr` into `U` and contracts the distance to `u*(μ)`
quadratically. Bundling `U ⊆ C_interior` into the basin conclusion
removes the need for a separate `rjnStepC_in_C` sorry — interior
preservation follows from set inclusion.

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
      U ⊆ 𝓢.C_interior ∧
      ∃ K : ℝ, 0 < K ∧
        (∀ u ∈ U, u ∈ 𝓢.sphere → 𝓢.rjnStepC μ u ∈ U) ∧
        (∀ u ∈ U, u ∈ 𝓢.sphere →
          ‖𝓢.rjnStepC μ u - 𝓢.centralPathPoint μ hμ‖ ≤
            K * ‖u - 𝓢.centralPathPoint μ hμ‖ ^ 2) := sorry

/-- **Interior preservation for Variant C.** For `u_k ∈ U` in the basin
of `rjnStepC_quadratic_basin`, the Newton step stays in `int C`.
Trivial once the basin theorem asserts `U ⊆ C_interior`. -/
theorem rjnStepC_in_C_of_basin {μ : ℝ} {u_k : H X Y}
    {U : Set (H X Y)} (hU_sub : U ⊆ 𝓢.C_interior)
    (h_basin : ∀ u ∈ U, u ∈ 𝓢.sphere → 𝓢.rjnStepC μ u ∈ U)
    (hu_k_U : u_k ∈ U) (hu_k_S : u_k ∈ 𝓢.sphere) :
    𝓢.rjnStepC μ u_k ∈ 𝓢.C_interior :=
  hU_sub (h_basin u_k hu_k_U hu_k_S)

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
with `rjnStepC_mem_sphere` (proven from `expMap_mem_sphere` and the
tangency of `rjnDirectionC`) into a recursive sequence. Interior
preservation falls out of `U ⊆ C_interior` (part of the basin
conclusion); only `rjnStepC_quadratic_basin` carries the deep analytic
sorry. -/
theorem rjnStepC_quadratic_convergence {μ : ℝ} (hμ : 0 < μ) :
    ∃ U : Set (H X Y), IsOpen U ∧ 𝓢.centralPathPoint μ hμ ∈ U ∧
      ∀ u₀ ∈ U, u₀ ∈ 𝓢.sphere → u₀ ∈ 𝓢.C_interior →
        ∃ seq : ℕ → H X Y,
          seq 0 = u₀ ∧
          (∀ k, seq k ∈ 𝓢.sphere ∩ 𝓢.C_interior) ∧
          ∃ K : ℝ, 0 < K ∧
            ∀ k, ‖seq (k+1) - 𝓢.centralPathPoint μ hμ‖ ≤
                   K * ‖seq k - 𝓢.centralPathPoint μ hμ‖ ^ 2 := by
  obtain ⟨U, hU_open, hU_mem, hU_sub, K, hK_pos, h_basin, h_contract⟩ :=
    𝓢.rjnStepC_quadratic_basin hμ
  refine ⟨U, hU_open, hU_mem, ?_⟩
  intros u₀ hu₀_U hu₀_S _
  let seq_fn : ℕ → H X Y := fun k =>
    Nat.rec u₀ (fun _ s => 𝓢.rjnStepC μ s) k
  have h_seq_succ : ∀ k, seq_fn (k + 1) = 𝓢.rjnStepC μ (seq_fn k) := fun _ => rfl
  have h_strong : ∀ k, seq_fn k ∈ U ∧ seq_fn k ∈ 𝓢.sphere := by
    intro k
    induction k with
    | zero => exact ⟨hu₀_U, hu₀_S⟩
    | succ k ih =>
      obtain ⟨h_U_k, h_S_k⟩ := ih
      refine ⟨?_, ?_⟩
      · rw [h_seq_succ]; exact h_basin _ h_U_k h_S_k
      · rw [h_seq_succ]; exact 𝓢.rjnStepC_mem_sphere h_S_k
  refine ⟨seq_fn, rfl, ?_, K, hK_pos, ?_⟩
  · intro k
    exact ⟨(h_strong k).2, hU_sub (h_strong k).1⟩
  · intro k
    obtain ⟨h_U_k, h_S_k⟩ := h_strong k
    rw [h_seq_succ]
    exact h_contract _ h_U_k h_S_k

end IrnSetup
end Irn
