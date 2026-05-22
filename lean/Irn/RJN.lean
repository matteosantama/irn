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

Paper Theorem 12 decomposes into two pieces by triangle inequality:

* **Tangent step bound** — the Newton-step half, itself split here
  into two independent analytic sorries:
  - `rjnDirection_linear_bound` — `‖rjnDirection μ u‖ ≤ C ‖u − u*‖`
    near `u*(μ)`; the IFT/Lipschitz half of paper Proposition 11.
  - `rjnDirection_tangent_step_quadratic_bound` —
    `‖u + rjnDirection μ u − u*‖ ≤ K_tan ‖u − u*‖²`; the Newton-
    identity + Taylor half (`Φ'(u*) = 0` on `T_{u*}Sr`).
* **Retraction bound** — the second-order retraction property of
  `expMap`: `‖expMap u v − (u + v)‖ ≤ ‖v‖²/r`. Proven in
  `Sphere.expMap_sub_add_norm_le` from the trigonometric identities.

`rjnDirection_quadratic_basin` combines the two analytic sorries and
shrinks the basin radius to satisfy `C·ε ≤ r` (so the retraction
bound applies on every step) and `ball u* ε ⊆ C_interior` (from
openness of `C_interior`). `rjnStep_quadratic_basin` is then derived
from it together with the retraction bound. -/

/-- **Local uniqueness of the Variant C tangent solution at `u*(μ)`.**
At `u_k = u*(μ)` the Riemannian semi-Newton tangent inclusion admits
`v = 0` as a solution (`IsRjnSolution_zero_at_centralPath`); this
lemma states `v = 0` is the *unique* such solution.

**Sorry.** Paper proof (§5.5): the closed-form λ-parametrisation
`u(λ) = w₀(λ) + θ(λ) w₁` reduces the Riemannian semi-Newton
inclusion to a scalar λ-quadratic (paper eq. `eq:lambda-quadratic-B`)
with at most two real roots. At `u_k = u*(μ)`, `λ = 0` yields
`u(0) = u*` (the central-path point itself), so `v(0) = 0`. The
IFT regime of paper Proposition 11 selects this `λ = 0` root as
the unique solution in a neighbourhood of `(u*, 0)`. -/
theorem IsRjnSolution_at_centralPath_unique {μ : ℝ} (hμ : 0 < μ)
    {v : H X Y}
    (_hv : 𝓢.IsRjnSolution μ (𝓢.centralPathPoint μ hμ) v) : v = 0 := sorry

/-- **The Newton direction vanishes at `u*(μ)`.** The base case of
the basin theorem: at the centre of the basin, `rjnDirection μ u* = 0`,
so both bounds in `rjnDirection_linear_bound` and
`rjnDirection_tangent_step_quadratic_bound` reduce to `0 ≤ 0`.
Combines `rjnDirection_isRjnSolution_at_centralPath` (the chosen
direction is a Variant C solution) with
`IsRjnSolution_at_centralPath_unique` (the only such solution is `0`). -/
theorem rjnDirection_at_centralPath_eq_zero {μ : ℝ} (hμ : 0 < μ) :
    𝓢.rjnDirection μ (𝓢.centralPathPoint μ hμ) = 0 :=
  𝓢.IsRjnSolution_at_centralPath_unique hμ
    (𝓢.rjnDirection_isRjnSolution_at_centralPath hμ)

/-- **Local Lipschitz continuity of `rjnDirection`** (sorry — paper
Proposition 11, IFT half). In a Euclidean ball around `u*(μ)`,
`rjnDirection μ` is Lipschitz with some constant `C`.

**Sorry.** Paper proof (Proposition 11): the Variant C tangent
inclusion in the bundle `(v, λ, θ)` is a `C¹` system in `u` whose
partial derivative in `(v, λ, θ)` at `(u*, 0, 0, θ*)` is invertible.
The implicit function theorem produces a `C¹` map `u ↦ (v(u), λ(u), θ(u))`
with `(v(u*), λ(u*), θ(u*)) = (0, 0, θ*)`; combined with the
uniqueness lemma `IsRjnSolution_at_centralPath_unique` (extended to a
neighbourhood by IFT-branch uniqueness), `v(u) = rjnDirection μ u` in
a neighbourhood of `u*`. Lipschitz continuity follows from the bounded
derivative of `v` on a compact ball. -/
theorem rjnDirection_locallyLipschitz {μ : ℝ} (hμ : 0 < μ) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
      ∀ u₁ u₂ : H X Y,
        u₁ ∈ Metric.ball (𝓢.centralPathPoint μ hμ) ε →
        u₂ ∈ Metric.ball (𝓢.centralPathPoint μ hμ) ε →
          ‖𝓢.rjnDirection μ u₁ - 𝓢.rjnDirection μ u₂‖ ≤ C * ‖u₁ - u₂‖ := sorry

/-- **Local linear bound on `rjnDirection`** (paper §5.6 Theorem 12,
IFT/Lipschitz half). In a basin of `u*(μ)`, the Newton direction
`rjnDirection μ u` is linearly bounded by the distance to `u*(μ)`.

Proven from `rjnDirection_at_centralPath_eq_zero` (base case
`rjnDirection μ u* = 0`) and `rjnDirection_locallyLipschitz` (sorry):
`‖rjnDirection μ u‖ = ‖rjnDirection μ u − rjnDirection μ u*‖
                    ≤ C ‖u − u*‖`. The sphere hypothesis is unused
here — it's threaded for compatibility with the basin signature. -/
theorem rjnDirection_linear_bound {μ : ℝ} (hμ : 0 < μ) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
      ∀ u : H X Y,
        u ∈ Metric.ball (𝓢.centralPathPoint μ hμ) ε → u ∈ 𝓢.sphere →
          ‖𝓢.rjnDirection μ u‖ ≤ C * ‖u - 𝓢.centralPathPoint μ hμ‖ := by
  obtain ⟨ε, C, hε_pos, hC_pos, h_lip⟩ := 𝓢.rjnDirection_locallyLipschitz hμ
  refine ⟨ε, C, hε_pos, hC_pos, ?_⟩
  intros u hu _
  have h_star_mem : 𝓢.centralPathPoint μ hμ ∈
      Metric.ball (𝓢.centralPathPoint μ hμ) ε := by
    rw [Metric.mem_ball, dist_self]; exact hε_pos
  have h := h_lip u (𝓢.centralPathPoint μ hμ) hu h_star_mem
  rw [𝓢.rjnDirection_at_centralPath_eq_zero hμ, sub_zero] at h
  exact h

/-- **Local quadratic bound on the tangent step** (sorry — paper §5.6
Theorem 12, Newton-identity half). In a basin of `u*(μ)`, the tangent
iterate `u + rjnDirection μ u` is quadratically close to `u*(μ)`.

**Sorry.** Paper proof: define `Φ(u) := u + rjnDirection μ u`. By the
IFT smoothness of `rjnDirection` near `u*` (same machinery as
`rjnDirection_linear_bound`), `Φ` is `C²` on a neighbourhood of `u*`.
The Newton identity in tangent coordinates gives `Φ(u*) = u*` (since
`rjnDirection μ u* = 0`) and `Φ'(u*) = 0` on `T_{u*}Sr`
(cancellation: the linearised Newton equation at `u*` solves
exactly). Taylor's theorem with `C²` remainder yields the quadratic
bound. -/
theorem rjnDirection_tangent_step_quadratic_bound {μ : ℝ} (hμ : 0 < μ) :
    ∃ ε K_tan : ℝ, 0 < ε ∧ 0 < K_tan ∧
      ∀ u : H X Y,
        u ∈ Metric.ball (𝓢.centralPathPoint μ hμ) ε → u ∈ 𝓢.sphere →
          ‖u + 𝓢.rjnDirection μ u - 𝓢.centralPathPoint μ hμ‖ ≤
            K_tan * ‖u - 𝓢.centralPathPoint μ hμ‖ ^ 2 := sorry

/-- **Tangent step quadratic basin** (paper §5.6 Theorem 12, "tangent
step" half). Combines the two analytic sorries
`rjnDirection_linear_bound` and `rjnDirection_tangent_step_quadratic_bound`
with the openness of `C_interior` to produce a single basin radius
`ε` satisfying:
* `C * ε ≤ r` — so `‖rjnDirection μ u‖ ≤ C ‖u − u*‖ < C ε ≤ r`
  on every point of the basin, making the retraction bound
  `expMap_sub_add_norm_le` applicable downstream;
* `ball u* ε ⊆ C_interior` — by openness of `C_interior` at the
  central-path point.

The combined `ε` is `min ε₁ (min ε₂ (min δ (r/C)))`, where `(ε₁, C)`
comes from the linear bound, `(ε₂, K_tan)` from the quadratic bound,
and `δ` is the openness radius of `C_interior` at `u*`. -/
theorem rjnDirection_quadratic_basin {μ : ℝ} (hμ : 0 < μ) :
    ∃ ε C K_tan : ℝ, 0 < ε ∧ 0 < C ∧ 0 < K_tan ∧
      C * ε ≤ 𝓢.r ∧
      Metric.ball (𝓢.centralPathPoint μ hμ) ε ⊆ 𝓢.C_interior ∧
      (∀ u : H X Y,
        u ∈ Metric.ball (𝓢.centralPathPoint μ hμ) ε → u ∈ 𝓢.sphere →
          ‖𝓢.rjnDirection μ u‖ ≤ C * ‖u - 𝓢.centralPathPoint μ hμ‖ ∧
          ‖u + 𝓢.rjnDirection μ u - 𝓢.centralPathPoint μ hμ‖ ≤
            K_tan * ‖u - 𝓢.centralPathPoint μ hμ‖ ^ 2) := by
  set u_star := 𝓢.centralPathPoint μ hμ with hu_star_def
  have hu_star_C : u_star ∈ 𝓢.C_interior :=
    (𝓢.centralPathPoint_isCentralPathPoint μ hμ).1
  obtain ⟨ε₁, C, hε₁_pos, hC_pos, h_lin⟩ := 𝓢.rjnDirection_linear_bound hμ
  obtain ⟨ε₂, K_tan, hε₂_pos, hK_tan_pos, h_quad⟩ :=
    𝓢.rjnDirection_tangent_step_quadratic_bound hμ
  obtain ⟨δ, hδ_pos, hδ_sub⟩ :=
    Metric.isOpen_iff.mp 𝓢.C_interior_isOpen u_star hu_star_C
  have hr_pos : 0 < 𝓢.r := 𝓢.r_pos
  have h_rC_pos : 0 < 𝓢.r / C := div_pos hr_pos hC_pos
  set ε : ℝ := min ε₁ (min ε₂ (min δ (𝓢.r / C))) with hε_def
  have hε_pos : 0 < ε :=
    lt_min hε₁_pos (lt_min hε₂_pos (lt_min hδ_pos h_rC_pos))
  have hε_le_ε₁ : ε ≤ ε₁ := min_le_left _ _
  have hε_le_ε₂ : ε ≤ ε₂ :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hε_le_δ : ε ≤ δ :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε_le_rC : ε ≤ 𝓢.r / C :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have h_Cε_le_r : C * ε ≤ 𝓢.r := by
    rw [mul_comm]
    exact (le_div_iff₀ hC_pos).mp hε_le_rC
  have h_ball_sub : Metric.ball u_star ε ⊆ 𝓢.C_interior :=
    subset_trans (Metric.ball_subset_ball hε_le_δ) hδ_sub
  refine ⟨ε, C, K_tan, hε_pos, hC_pos, hK_tan_pos, h_Cε_le_r, h_ball_sub, ?_⟩
  intros u hu_ball hu_S
  have h_in_ε₁ : u ∈ Metric.ball u_star ε₁ :=
    Metric.ball_subset_ball hε_le_ε₁ hu_ball
  have h_in_ε₂ : u ∈ Metric.ball u_star ε₂ :=
    Metric.ball_subset_ball hε_le_ε₂ hu_ball
  exact ⟨h_lin u h_in_ε₁ hu_S, h_quad u h_in_ε₂ hu_S⟩

/-- **Quadratic basin from tangent + retraction.** Combines
`rjnDirection_quadratic_basin` (the tangent step half, derived from
two analytic sorries) with `Sphere.expMap_sub_add_norm_le` (the
retraction half, proven) via triangle inequality. The combined
contraction constant is `K = C² / r + K_tan`; the self-mapping basin
shrinks to `min(ε, 1/(2K))/2`. -/
theorem rjnStep_quadratic_basin {μ : ℝ} (hμ : 0 < μ) :
    ∃ U : Set (H X Y), IsOpen U ∧ 𝓢.centralPathPoint μ hμ ∈ U ∧
      U ⊆ 𝓢.C_interior ∧
      ∃ K : ℝ, 0 < K ∧
        (∀ u ∈ U, u ∈ 𝓢.sphere → 𝓢.rjnStep μ u ∈ U) ∧
        (∀ u ∈ U, u ∈ 𝓢.sphere →
          ‖𝓢.rjnStep μ u - 𝓢.centralPathPoint μ hμ‖ ≤
            K * ‖u - 𝓢.centralPathPoint μ hμ‖ ^ 2) := by
  obtain ⟨ε, C, K_tan, hε_pos, hC_pos, hK_tan_pos, hCε_le_r, hε_sub, h_tan⟩ :=
    𝓢.rjnDirection_quadratic_basin hμ
  set u_star := 𝓢.centralPathPoint μ hμ
  have hr_pos : 0 < 𝓢.r := 𝓢.r_pos
  -- Combined contraction constant K = C² / r + K_tan.
  set K : ℝ := C ^ 2 / 𝓢.r + K_tan with hK_def
  have hK_pos : 0 < K := by
    have h_C2_div : 0 < C ^ 2 / 𝓢.r := div_pos (by positivity) hr_pos
    linarith
  -- Shrink ε to make the basin self-mapping: ε' := min(ε, 1/(2K)) / 2.
  set ε' : ℝ := min ε (1 / (2 * K)) / 2 with hε'_def
  have h_2K_pos : 0 < 2 * K := by linarith
  have h_1_2K_pos : 0 < 1 / (2 * K) := by positivity
  have hε'_pos : 0 < ε' := by
    apply div_pos _ (by norm_num)
    exact lt_min hε_pos h_1_2K_pos
  have hε'_le_ε : ε' ≤ ε := by
    calc ε' = min ε (1 / (2 * K)) / 2 := rfl
      _ ≤ ε / 2 := by gcongr; exact min_le_left _ _
      _ ≤ ε := by linarith
  have hε'_le : ε' ≤ 1 / (2 * K) := by
    calc ε' = min ε (1 / (2 * K)) / 2 := rfl
      _ ≤ (1 / (2 * K)) / 2 := by gcongr; exact min_le_right _ _
      _ ≤ 1 / (2 * K) := by linarith
  set U : Set (H X Y) := Metric.ball u_star ε' with hU_def
  have hU_open : IsOpen U := Metric.isOpen_ball
  have hU_mem : u_star ∈ U := by
    rw [hU_def, Metric.mem_ball, dist_self]; exact hε'_pos
  -- U ⊆ C_interior: U ⊆ ball u_star ε ⊆ C_interior.
  have hU_sub : U ⊆ 𝓢.C_interior := by
    refine subset_trans ?_ hε_sub
    intro u hu
    rw [Metric.mem_ball] at hu ⊢
    exact lt_of_lt_of_le hu hε'_le_ε
  -- The per-point bound for u ∈ U ∩ sphere.
  have h_perpoint : ∀ u ∈ U, u ∈ 𝓢.sphere →
      ‖𝓢.rjnStep μ u - u_star‖ ≤ K * ‖u - u_star‖ ^ 2 := by
    intros u hu_U hu_S
    have hu_ε : u ∈ Metric.ball u_star ε := by
      rw [Metric.mem_ball] at hu_U ⊢
      exact lt_of_lt_of_le hu_U hε'_le_ε
    obtain ⟨h_dir_bd, h_tangent_bd⟩ := h_tan u hu_ε hu_S
    have h_dist : ‖u - u_star‖ < ε := by
      have := hu_ε
      rw [Metric.mem_ball, dist_eq_norm] at this
      exact this
    -- ‖rjnDirection μ u‖ ≤ C * ‖u - u_star‖ < C * ε ≤ r.
    have h_dir_lt_r : ‖𝓢.rjnDirection μ u‖ < 𝓢.r := by
      have h1 : C * ‖u - u_star‖ < C * ε :=
        mul_lt_mul_of_pos_left h_dist hC_pos
      linarith [h_dir_bd]
    have h_dir_le_r : ‖𝓢.rjnDirection μ u‖ ≤ 𝓢.r := le_of_lt h_dir_lt_r
    -- Retraction bound.
    have h_ret :=
      𝓢.expMap_sub_add_norm_le hu_S (𝓢.rjnDirection_tangent μ u) h_dir_le_r
    -- rjnStep μ u = expMap u (rjnDirection μ u).
    have h_step_eq : 𝓢.rjnStep μ u = 𝓢.expMap u (𝓢.rjnDirection μ u) := rfl
    rw [h_step_eq]
    -- Triangle inequality:
    -- ‖expMap u v - u_star‖ ≤ ‖expMap u v - (u + v)‖ + ‖(u + v) - u_star‖
    have h_tri : ‖𝓢.expMap u (𝓢.rjnDirection μ u) - u_star‖ ≤
        ‖𝓢.expMap u (𝓢.rjnDirection μ u) - (u + 𝓢.rjnDirection μ u)‖ +
          ‖(u + 𝓢.rjnDirection μ u) - u_star‖ := by
      have h_eq : 𝓢.expMap u (𝓢.rjnDirection μ u) - u_star =
          (𝓢.expMap u (𝓢.rjnDirection μ u) - (u + 𝓢.rjnDirection μ u)) +
          ((u + 𝓢.rjnDirection μ u) - u_star) := by abel
      rw [h_eq]
      exact norm_add_le _ _
    -- ‖expMap u v - (u + v)‖ ≤ ‖v‖²/r ≤ (C ‖u - u_star‖)²/r = C² ‖u - u_star‖²/r.
    have h_ret_quad : ‖𝓢.rjnDirection μ u‖ ^ 2 / 𝓢.r ≤
        C ^ 2 * ‖u - u_star‖ ^ 2 / 𝓢.r := by
      have h_dir_nn : 0 ≤ ‖𝓢.rjnDirection μ u‖ := norm_nonneg _
      have h_C_uu_nn : 0 ≤ C * ‖u - u_star‖ :=
        mul_nonneg hC_pos.le (norm_nonneg _)
      have h_sq_le : ‖𝓢.rjnDirection μ u‖ ^ 2 ≤ (C * ‖u - u_star‖) ^ 2 :=
        pow_le_pow_left₀ h_dir_nn h_dir_bd 2
      have h_C2 : (C * ‖u - u_star‖) ^ 2 = C ^ 2 * ‖u - u_star‖ ^ 2 := by ring
      rw [h_C2] at h_sq_le
      exact div_le_div_of_nonneg_right h_sq_le hr_pos.le
    -- Combine.
    calc ‖𝓢.expMap u (𝓢.rjnDirection μ u) - u_star‖
        ≤ ‖𝓢.expMap u (𝓢.rjnDirection μ u) - (u + 𝓢.rjnDirection μ u)‖ +
            ‖(u + 𝓢.rjnDirection μ u) - u_star‖ := h_tri
      _ ≤ ‖𝓢.rjnDirection μ u‖ ^ 2 / 𝓢.r + K_tan * ‖u - u_star‖ ^ 2 := by
          gcongr
      _ ≤ C ^ 2 * ‖u - u_star‖ ^ 2 / 𝓢.r + K_tan * ‖u - u_star‖ ^ 2 := by
          linarith
      _ = K * ‖u - u_star‖ ^ 2 := by
          rw [hK_def]; ring
  -- Self-mapping: u ∈ U ⟹ rjnStep μ u ∈ U.
  refine ⟨U, hU_open, hU_mem, hU_sub, K, hK_pos, ?_, h_perpoint⟩
  intros u hu_U hu_S
  have h_bd := h_perpoint u hu_U hu_S
  have h_dist : ‖u - u_star‖ < ε' := by
    have := hu_U
    rw [Metric.mem_ball, dist_eq_norm] at this
    exact this
  -- ‖rjnStep μ u - u_star‖ ≤ K * ε'² ≤ K * (1/(2K)) * ε' ≤ ε'/2 < ε'.
  have h_dist_nn : 0 ≤ ‖u - u_star‖ := norm_nonneg _
  have hε'_nn : 0 ≤ ε' := hε'_pos.le
  have h_sq_lt : ‖u - u_star‖ ^ 2 < ε' ^ 2 := by
    have : ‖u - u_star‖ ^ 2 ≤ ε' ^ 2 :=
      pow_le_pow_left₀ h_dist_nn h_dist.le 2
    have h_ne : ‖u - u_star‖ ^ 2 ≠ ε' ^ 2 := by
      intro h_eq
      have : ‖u - u_star‖ = ε' := by
        have := h_eq
        nlinarith [h_dist_nn, hε'_nn]
      linarith
    exact lt_of_le_of_ne this h_ne
  have h_K_dist_sq_le : K * ‖u - u_star‖ ^ 2 ≤ K * ε' ^ 2 := by
    exact mul_le_mul_of_nonneg_left h_sq_lt.le hK_pos.le
  have h_Kε'_sq : K * ε' ^ 2 ≤ ε' / 2 := by
    -- K * ε'² ≤ K * ε' * ε' ≤ (1/2) * ε' (using ε' ≤ 1/(2K), so K * ε' ≤ 1/2)
    have h_K_ε' : K * ε' ≤ 1 / 2 := by
      have h_le := hε'_le  -- ε' ≤ 1/(2K)
      have h_mul : K * ε' ≤ K * (1 / (2 * K)) :=
        mul_le_mul_of_nonneg_left h_le hK_pos.le
      have h_simp : K * (1 / (2 * K)) = 1 / 2 := by
        field_simp
      linarith
    have hε'_sq_eq : K * ε' ^ 2 = K * ε' * ε' := by ring
    rw [hε'_sq_eq]
    have : K * ε' * ε' ≤ (1 / 2) * ε' :=
      mul_le_mul_of_nonneg_right h_K_ε' hε'_nn
    linarith
  have h_total : ‖𝓢.rjnStep μ u - u_star‖ < ε' := by
    calc ‖𝓢.rjnStep μ u - u_star‖
        ≤ K * ‖u - u_star‖ ^ 2 := h_bd
      _ ≤ K * ε' ^ 2 := h_K_dist_sq_le
      _ ≤ ε' / 2 := h_Kε'_sq
      _ < ε' := by linarith
  rw [Metric.mem_ball, dist_eq_norm]
  exact h_total

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
falls out of `U ⊆ C_interior`. The analytic sorries remaining in this
proof chain are `IsRjnSolution_at_centralPath_unique`,
`rjnDirection_locallyLipschitz`, and
`rjnDirection_tangent_step_quadratic_bound` (all under paper
Proposition 11 / Theorem 12); the retraction half is fully formalized
in `Sphere.expMap_sub_add_norm_le`. -/
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
