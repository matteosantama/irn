/-
# Riemannian Semi-Newton on `Sr` (paper §5)

The Riemannian semi-Newton step for solving `T_μ(u) = 0` on the sphere
`Sr ⊆ H`. The step is built from:

* a **partial linearisation** of the smooth summand `h(u) = μ u + μ ∇F*(u)`
  around the current iterate (the "semi" of semi-Newton);
* an **exact closed-form inverse** of `H_k + Ψ` (paper §4 Theorem 9)
  for the non-linearised summand `Ψ(u) = Q(u) + μ ∇G*(u)`;
* a **Lagrange multiplier `λ_k`** enforcing tangency to `Sr` at `u_k`;
* a **closed-form geodesic retraction** `exp_{u_k}` of `Sr` (paper
  Proposition 10) to land the next iterate back on `Sr` exactly.

This is *the* method described in paper §5 — there is no longer a
"Variant C" label, the alternative constraint/retraction pairs are
appendix material only.

Paper references:
* §5.1 eq. `eq:splitting`        — splitting `T_μ = h + Ψ`
* §5.3 eq. `eq:rjn`              — Riemannian semi-Newton step
* §5.3 Proposition 10            — exact sphericity of `exp_u`
                                  (see `Sphere.expMap_mem_sphere`)
* §5.5 Proposition 11            — existence and local uniqueness of `λ_k`
* §5.6 Theorem 12                — local quadratic convergence
-/

import Irn.Sphere

namespace Irn
namespace IrnSetup

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
variable (𝓢 : IrnSetup X Y)

open scoped InnerProductSpace

/-- The smooth summand `h(u) = μ u + μ ∇F*(u)` of the splitting
`T_μ = h + Ψ` (paper §5.1 eq. `eq:splitting`). -/
noncomputable def h (μ : ℝ) (u : H X Y) : H X Y :=
  μ • u + μ • 𝓢.φ u

/-! ### The Newton direction (paper §5.3 eq. `eq:rjn`)

The Riemannian semi-Newton tangent equation at `u_k ∈ Sr ∩ int C`,
level `μ > 0`, asks for `v_k ∈ T_{u_k}Sr` together with a Lagrange
multiplier `λ_k ∈ ℝ` and a scalar `θ_k > 0` such that

  `(H_k + M)(u_k + v_k) = H_k u_k − h(u_k) − λ_k u_k + θ_k e_τ`,
  `θ_k · τ(u_k + v_k) = Pₓ(u_k + v_k, u_k + v_k) + μ`,
  `u_k⊤ v_k = 0`,
  `u_k + v_k ∈ C_+`,

with `H_k = μ I + μ ∇²F*(u_k)` and `h(u_k) = μ u_k + μ ∇F*(u_k)`. The
first two lines are the closed-form inverse of paper Theorem 9 at the
`λ`-shifted input `z(λ_k) = u_k − H_k⁻¹(h(u_k) + λ_k u_k)` of paper
§5.4; the third is the tangency constraint `C_B(u_k + v_k) = 0`
rewritten using `‖u_k‖² = ν + 1`. -/

/-- **`IsRjnSolution μ u_k v`** — the property that `v` is a Riemannian
semi-Newton tangent direction at `(μ, u_k)`. Packages tangency, cone
membership of `u_k + v`, and existence of compatible scalars `(λ, θ)`
satisfying the closed-form-inverse equations of paper §5.4. -/
def IsRjnSolution (𝓢 : IrnSetup X Y) (μ : ℝ) (u_k v : H X Y) : Prop :=
  inner ℝ u_k v = (0 : ℝ) ∧
  (u_k + v) ∈ 𝓢.Cplus ∧
  ∃ θ : ℝ, 0 < θ ∧ ∃ lam : ℝ,
    (𝓢.hessian_h μ u_k + 𝓢.M_clm) (u_k + v) =
      𝓢.hessian_h μ u_k u_k -
        (μ • u_k + μ • 𝓢.f_lhscb.grad u_k + lam • u_k) +
        θ • 𝓢.e_τ ∧
    θ * 𝓢.tau_proj (u_k + v) =
      𝓢.Px_bilinform_clm (u_k + v) (u_k + v) + μ

/-- **The trivial Newton direction at the central-path point.** At
`u_k = u*(μ)` the fixed-point property `T_μ(u_k) = 0` forces `v_k = 0`,
`λ_k = 0`, `θ_k = (Pₓ(u_k, u_k) + μ) / τ(u_k)`. Concretely:
* tangency `⟨u_k, 0⟩ = 0` is trivial;
* `u_k + 0 = u_k ∈ C_+` from `u_k ∈ int C`;
* the Newton equation reduces to `M u_k + h(u_k) = θ_k e_τ`, which
  follows from `T_μ(u_k) = Q(u_k) + h(u_k) - (μ/τ) e_τ = 0` plus
  `Q(u_k) = M u_k - (Pₓ/τ) e_τ`;
* the scalar equation `θ_k · τ(u_k) = Pₓ(u_k, u_k) + μ` is the
  definition of `θ_k`. -/
theorem IsRjnSolution_zero_at_centralPath (𝓢 : IrnSetup X Y) {μ : ℝ}
    (hμ : 0 < μ) :
    𝓢.IsRjnSolution μ (𝓢.centralPathPoint μ hμ) 0 := by
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
    -- (H_k + M_clm)(u_k + 0) = H_k u_k − (μ•u_k + μ•∇F*(u_k) + 0•u_k) + θ•e_τ.
    show (𝓢.hessian_h μ u_k + 𝓢.M_clm) (u_k + 0) =
      𝓢.hessian_h μ u_k u_k -
        (μ • u_k + μ • 𝓢.f_lhscb.grad u_k + (0 : ℝ) • u_k) +
        θ • 𝓢.e_τ
    rw [add_zero, zero_smul, add_zero, ContinuousLinearMap.add_apply]
    -- Reduce to: M_clm u_k = θ•e_τ − (μ•u_k + μ•∇F*(u_k)).
    have h_Q : 𝓢.Q u_k =
        𝓢.M_clm u_k - (𝓢.Px_bilinform_clm u_k u_k / 𝓢.tau_proj u_k) • 𝓢.e_τ := by
      show 𝓢.M_apply u_k - _ • _ = 𝓢.M_clm u_k - _ • _
      rw [show 𝓢.M_apply u_k = 𝓢.M_clm u_k from rfl, hPx_clm_apply]
    have h_φ : 𝓢.φ u_k = 𝓢.f_lhscb.grad u_k + (-1 / 𝓢.tau_proj u_k) • 𝓢.e_τ := rfl
    have h_T_unfolded : 𝓢.Q u_k + μ • u_k + μ • 𝓢.φ u_k = 0 := hT
    rw [h_Q, h_φ] at h_T_unfolded
    -- The θ•e_τ coefficient combines: −(Pₓ/τ) − μ·(−1/τ) = −(Pₓ+μ)/τ = −θ.
    have h_coef : (-(𝓢.Px_bilinform_clm u_k u_k / 𝓢.tau_proj u_k))
                  + μ * (-1 / 𝓢.tau_proj u_k) = -θ := by
      rw [hθ_def]; field_simp; ring
    have h_T_rearranged :
        𝓢.M_clm u_k + μ • u_k + μ • 𝓢.f_lhscb.grad u_k = θ • 𝓢.e_τ := by
      have h := h_T_unfolded
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
      have h_neg : 𝓢.M_clm u_k + μ • u_k + μ • 𝓢.f_lhscb.grad u_k =
          -((-θ) • 𝓢.e_τ) := eq_neg_of_add_eq_zero_left h
      rw [h_neg, neg_smul, neg_neg]
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

/-- **The Riemannian semi-Newton direction.** Constructive total
function: returns the (Classical-choose-extracted) tangent direction
satisfying `IsRjnSolution` when one exists, otherwise falls back to
`0`. The existence branch covers at least `u_k = u*(μ)` (via
`IsRjnSolution_zero_at_centralPath`); the extension to a full
neighbourhood of `u*(μ)` is paper Proposition 11 and is reached
through the `Classical.choose` mechanism. -/
noncomputable def rjnDirection (𝓢 : IrnSetup X Y) (μ : ℝ) (u_k : H X Y) :
    H X Y :=
  haveI : Decidable (∃ v, 𝓢.IsRjnSolution μ u_k v) := Classical.dec _
  if h : ∃ v, 𝓢.IsRjnSolution μ u_k v then Classical.choose h else 0

/-- `rjnDirection` either satisfies `IsRjnSolution` (when a solution
exists) or is `0` (fallback). -/
theorem rjnDirection_isRjnSolution_or_zero (𝓢 : IrnSetup X Y)
    (μ : ℝ) (u_k : H X Y) :
    𝓢.IsRjnSolution μ u_k (𝓢.rjnDirection μ u_k) ∨
      𝓢.rjnDirection μ u_k = 0 := by
  unfold rjnDirection
  split_ifs with h
  · exact Or.inl (Classical.choose_spec h)
  · exact Or.inr rfl

/-- At `u_k = u*(μ)`, `rjnDirection` lands in the existence branch —
i.e., it is an actual Riemannian semi-Newton direction (not the
fallback). Follows from `IsRjnSolution_zero_at_centralPath`. -/
theorem rjnDirection_isRjnSolution_at_centralPath (𝓢 : IrnSetup X Y)
    {μ : ℝ} (hμ : 0 < μ) :
    𝓢.IsRjnSolution μ (𝓢.centralPathPoint μ hμ)
      (𝓢.rjnDirection μ (𝓢.centralPathPoint μ hμ)) := by
  unfold rjnDirection
  have h : ∃ v, 𝓢.IsRjnSolution μ (𝓢.centralPathPoint μ hμ) v :=
    ⟨0, 𝓢.IsRjnSolution_zero_at_centralPath hμ⟩
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- **Tangency of the Riemannian semi-Newton direction**:
`⟨u_k, v_k⟩ = 0`. Proven unconditionally by case-splitting on whether
`IsRjnSolution` holds — in the existence branch tangency comes from
the first conjunct of the predicate, in the fallback branch
`v_k = 0` is trivially tangent. -/
theorem rjnDirection_tangent (𝓢 : IrnSetup X Y) (μ : ℝ) (u_k : H X Y) :
    inner ℝ u_k (𝓢.rjnDirection μ u_k) = (0 : ℝ) := by
  rcases 𝓢.rjnDirection_isRjnSolution_or_zero μ u_k with h | h
  · exact h.1
  · rw [h]; exact inner_zero_right _

/-! ### The Riemannian semi-Newton step -/

/-- **The Riemannian semi-Newton step** (paper §5.3 eq. `eq:rjn` plus
the retraction `eq:retraction`): solve the tangent equation for
`v_k ∈ T_{u_k}Sr`, then retract back to `Sr` along the geodesic. -/
noncomputable def rjnStep (μ : ℝ) (u_k : H X Y) : H X Y :=
  𝓢.expMap u_k (𝓢.rjnDirection μ u_k)

/-- **Sphericity of the iterate**: the step preserves `Sr`. Combines
tangency of the Newton direction (`rjnDirection_tangent`) with the
exact-sphere property of `exp_u` (`expMap_mem_sphere`, paper
Proposition 10). -/
theorem rjnStep_mem_sphere {μ : ℝ} {u_k : H X Y} (hu_k : u_k ∈ 𝓢.sphere) :
    𝓢.rjnStep μ u_k ∈ 𝓢.sphere :=
  𝓢.expMap_mem_sphere u_k _ hu_k (𝓢.rjnDirection_tangent μ u_k)

/-! ### Quadratic contraction basin (paper §5.6 Theorem 12)

The analytic core of Theorem 12. Existence of an open basin
`U ⊆ C_interior` around `u*(μ)` such that one Riemannian semi-Newton
step maps `U ∩ Sr` into `U` and contracts the Euclidean distance to
`u*(μ)` quadratically. Bundling `U ⊆ C_interior` into the basin
conclusion makes interior preservation a set-inclusion consequence.

**Paper proof sketch (Theorem 12).** The tangent solver is a fixed-point
map `Φ : u_k ↦ u_k + v_k` with `Φ(u*) = u*` and `Φ'(u*) = 0` on
`T_{u*}Sr` (the Riemannian Jacobian `J* = P_{u*}(∇h(u*) + ∇Ψ(u*)) P_{u*}`
is `μ`-coercive, and the first-order term of `Φ` cancels by Newton's
identity). The Taylor remainder gives `‖u_k + v_k − u*‖ = O(‖u_k − u*‖²)`.
The geodesic retraction is second-order, adding only `O(‖v_k‖²) =
O(‖u_k − u*‖²)`. Combining yields the quadratic rate.

The full Lean proof requires Mathlib-level infrastructure not yet in
place: a Newton–Kantorovich theorem with self-concordant Lipschitz
control of `∇²F*` (paper §6.3 step (i); see
`LHSCB.hessian_dikin_bound` — also a sorry), and Riemannian Newton on
embedded submanifolds. -/
theorem rjnStep_quadratic_basin {μ : ℝ} (hμ : 0 < μ) :
    ∃ U : Set (H X Y), IsOpen U ∧ 𝓢.centralPathPoint μ hμ ∈ U ∧
      U ⊆ 𝓢.C_interior ∧
      ∃ K : ℝ, 0 < K ∧
        (∀ u ∈ U, u ∈ 𝓢.sphere → 𝓢.rjnStep μ u ∈ U) ∧
        (∀ u ∈ U, u ∈ 𝓢.sphere →
          ‖𝓢.rjnStep μ u - 𝓢.centralPathPoint μ hμ‖ ≤
            K * ‖u - 𝓢.centralPathPoint μ hμ‖ ^ 2) := sorry

/-- **Interior preservation.** For `u_k ∈ U` in the basin of
`rjnStep_quadratic_basin`, the next iterate stays in `int C`. Trivial
once the basin asserts `U ⊆ C_interior`. -/
theorem rjnStep_in_C_of_basin {μ : ℝ} {u_k : H X Y}
    {U : Set (H X Y)} (hU_sub : U ⊆ 𝓢.C_interior)
    (h_basin : ∀ u ∈ U, u ∈ 𝓢.sphere → 𝓢.rjnStep μ u ∈ U)
    (hu_k_U : u_k ∈ U) (hu_k_S : u_k ∈ 𝓢.sphere) :
    𝓢.rjnStep μ u_k ∈ 𝓢.C_interior :=
  hU_sub (h_basin u_k hu_k_U hu_k_S)

/-! ### Theorem 12 — local quadratic convergence -/

/-- **Theorem 12 (Local quadratic convergence).** Assume `f ∈ C³(int K)`
(encoded as `𝓢.d ≥ 3`, automatic). For each `μ > 0` there is an open
neighbourhood `U` of `u*(μ)` in `H` and a constant `K > 0` such that,
starting from any `u₀ ∈ U ∩ Sr ∩ int C`, the iterates
`u_{k+1} := rjnStep μ u_k` stay in `Sr ∩ int C` and satisfy
`‖u_{k+1} − u*(μ)‖ ≤ K · ‖u_k − u*(μ)‖²`.

Packages the basin theorem `rjnStep_quadratic_basin` together with
`rjnStep_mem_sphere` into a recursive sequence; interior preservation
falls out of `U ⊆ C_interior`. The only deep analytic sorry is
`rjnStep_quadratic_basin`. -/
theorem rjnStep_quadratic_convergence {μ : ℝ} (hμ : 0 < μ) :
    ∃ U : Set (H X Y), IsOpen U ∧ 𝓢.centralPathPoint μ hμ ∈ U ∧
      ∀ u₀ ∈ U, u₀ ∈ 𝓢.sphere → u₀ ∈ 𝓢.C_interior →
        ∃ seq : ℕ → H X Y,
          seq 0 = u₀ ∧
          (∀ k, seq k ∈ 𝓢.sphere ∩ 𝓢.C_interior) ∧
          ∃ K : ℝ, 0 < K ∧
            ∀ k, ‖seq (k+1) - 𝓢.centralPathPoint μ hμ‖ ≤
                   K * ‖seq k - 𝓢.centralPathPoint μ hμ‖ ^ 2 := by
  obtain ⟨U, hU_open, hU_mem, hU_sub, K, hK_pos, h_basin, h_contract⟩ :=
    𝓢.rjnStep_quadratic_basin hμ
  refine ⟨U, hU_open, hU_mem, ?_⟩
  intros u₀ hu₀_U hu₀_S _
  let seq_fn : ℕ → H X Y := fun k =>
    Nat.rec u₀ (fun _ s => 𝓢.rjnStep μ s) k
  have h_seq_succ : ∀ k, seq_fn (k + 1) = 𝓢.rjnStep μ (seq_fn k) := fun _ => rfl
  have h_strong : ∀ k, seq_fn k ∈ U ∧ seq_fn k ∈ 𝓢.sphere := by
    intro k
    induction k with
    | zero => exact ⟨hu₀_U, hu₀_S⟩
    | succ k ih =>
      obtain ⟨h_U_k, h_S_k⟩ := ih
      refine ⟨?_, ?_⟩
      · rw [h_seq_succ]; exact h_basin _ h_U_k h_S_k
      · rw [h_seq_succ]; exact 𝓢.rjnStep_mem_sphere h_S_k
  refine ⟨seq_fn, rfl, ?_, K, hK_pos, ?_⟩
  · intro k
    exact ⟨(h_strong k).2, hU_sub (h_strong k).1⟩
  · intro k
    obtain ⟨h_U_k, h_S_k⟩ := h_strong k
    rw [h_seq_succ]
    exact h_contract _ h_U_k h_S_k

end IrnSetup
end Irn
