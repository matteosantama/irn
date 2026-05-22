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
* §5.5 Proposition 11            — global uniqueness of `λ_k` (part a)
                                  and local existence + smoothness (part b)
* §5.6 Theorem 12                — local quadratic convergence
-/

import Irn.Sphere

namespace Irn
namespace IrnSetup

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
variable (𝓢 : IrnSetup X Y)

open scoped InnerProductSpace ContDiff

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
theorem IsRjnSolution.zero_at_centralPath (𝓢 : IrnSetup X Y) {μ : ℝ}
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
`IsRjnSolution.zero_at_centralPath`); local existence on a
neighbourhood of `u*(μ)` is paper Proposition 11(b). Global
uniqueness from paper Proposition 11(a) (`IsRjnSolution.unique`)
makes the `Classical.choose` value canonical wherever a solution
exists, not merely well-defined. -/
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
fallback). Follows from `IsRjnSolution.zero_at_centralPath`. -/
theorem rjnDirection_isRjnSolution_at_centralPath (𝓢 : IrnSetup X Y)
    {μ : ℝ} (hμ : 0 < μ) :
    𝓢.IsRjnSolution μ (𝓢.centralPathPoint μ hμ)
      (𝓢.rjnDirection μ (𝓢.centralPathPoint μ hμ)) := by
  unfold rjnDirection
  have h : ∃ v, 𝓢.IsRjnSolution μ (𝓢.centralPathPoint μ hμ) v :=
    ⟨0, IsRjnSolution.zero_at_centralPath 𝓢 hμ⟩
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

/-! ### Global uniqueness of the RJN tangent direction (paper §5.5
Proposition 11(a))

Paper Proposition 11(a) gives **global uniqueness** of the Lagrange
multiplier `λ_k` (and hence of `v_k`) on the full domain
`u_k ∈ Sr ∩ int C`, without any neighbourhood hypothesis. The proof
is short:

1. By the closed-form-inverse machinery of paper Theorem 9
   (`resolvent_closed_form` in `Irn.Resolvent`), for every `λ ∈ ℝ`
   the shifted equation
   `H_k(u_{k+1} - u_k) + h(u_k) + λ • u_k + Ψ(u_{k+1}) = 0`
   has a unique single-valued solution `u_{k+1}(λ) ∈ C_+`, smooth
   in `λ`.
2. Differentiating in `λ` and using `μ`-strong monotonicity of
   `A(λ) := H_k + ∇Ψ(u_{k+1}(λ))` (LHSCB + monotone `∇Ψ`):
   ```
   φ'(λ) := d/dλ ⟨u_k, u_{k+1}(λ)⟩
          = -⟨u_k, A(λ)⁻¹ u_k⟩ < 0,
   ```
   strictly, for every `λ ∈ ℝ` and every `u_k ∈ Sr ∩ int C`
   (using `u_k ≠ 0` from `‖u_k‖² = ν+1 > 0`).
3. The tangency residual
   `φ(λ) := ⟨u_k, u_{k+1}(λ)⟩ - (ν+1) = ⟨u_k, v(λ)⟩`
   (the last equality on the sphere) is therefore strictly
   decreasing on `ℝ`, hence has at most one zero — proving global
   uniqueness of `λ_k`, and via the single-valuedness of step (1),
   of `v_k`. -/

set_option maxHeartbeats 1600000 in
/-- **Global uniqueness of the RJN tangent direction** (paper
§5.5 Proposition 11(a)). For every `u_k ∈ Sr ∩ int C`, at most one
`v` satisfies `IsRjnSolution μ u_k v`.

**Proof.** Subtract the Newton equations of two `IsRjnSolution`
witnesses for `v₁, v₂` (set `u_i := u_k + v_i`, `Δu := u₁ - u₂`):
```
  (H_k + M) Δu = (θ₁ - θ₂) • e_τ - (λ₁ - λ₂) • u_k.
```
Inner-product with `Δu`. Tangency `⟨u_k, v_i⟩ = 0` kills the
`u_k`-coefficient; on the right, `⟨Δu, e_τ⟩ = τ(Δu)`. On the left,
`⟨Δu, (H_k + M) Δu⟩ = μ W_quad(u_k, Δu) + Px(Δu, Δu)`. So
```
  μ W_quad + Px(Δu, Δu) = (θ₁ - θ₂) τ(Δu).             (♠)
```
Subtract the two scalar equations
`θ_i τ_i = Px(u_i, u_i) + μ` and combine via the bilinear identity
`Px(u₁ + u₂, u₁ - u₂) = Px(u₁, u₁) - Px(u₂, u₂)` and the algebraic
identity `(θ₁ - θ₂)(τ₁ + τ₂) + (θ₁ + θ₂)(τ₁ - τ₂) = 2(θ₁ τ₁ - θ₂ τ₂)`
to get
```
  (θ₁ - θ₂)(τ₁ + τ₂) + (θ₁ + θ₂) τ(Δu) = 2 Px(u₁+u₂, Δu).   (♣)
```
Eliminating `θ₁ - θ₂` between (♠) and (♣) (multiply (♠) by `τ₁+τ₂`,
substitute via (♣)) gives, after multiplying by `τ₁+τ₂` once more,
```
  (τ₁+τ₂)² μ W_quad + (τ₁+τ₂)² Px(Δu, Δu) + (τ₁+τ₂)(θ₁+θ₂) τ(Δu)²
    = 2 (τ₁+τ₂) τ(Δu) Px(u₁+u₂, Δu).
```
The PSD bound `Px_quad_form_psd` applied at
`(x_proj(u₁+u₂), x_proj Δu, τ₁+τ₂, τ(Δu))` bounds the right side by
`τ(Δu)² Px(u₁+u₂, u₁+u₂) + (τ₁+τ₂)² Px(Δu, Δu)`. Cancelling the
`Px(Δu, Δu)`-terms,
```
  (τ₁+τ₂)² μ W_quad + (τ₁+τ₂)(θ₁+θ₂) τ(Δu)² ≤ τ(Δu)² Px(u₁+u₂, u₁+u₂).
```
A second PSD application at `(x_proj u₂, x_proj u₁, τ₂, τ₁)`,
combined with `Px(u_i, u_i) = θ_i τ_i - μ` and the AM-GM identity
`τ₁² + τ₂² ≥ 2 τ₁ τ₂`, gives
```
  τ₁ θ₂ + τ₂ θ₁ - 2 Px(u₁, u₂) ≥ 2 μ,
```
hence `Px(u₁+u₂, u₁+u₂) ≤ (τ₁+τ₂)(θ₁+θ₂) - 4μ`. Multiplying by
`τ(Δu)² ≥ 0` and substituting yields
```
  (τ₁+τ₂)² μ W_quad + 4 μ τ(Δu)² ≤ 0.
```
Both summands are non-negative (`τ_i, μ > 0`, `W_quad ≥ ‖·‖² ≥ 0`),
so both vanish. From `(τ₁+τ₂)² μ W_quad = 0` and `τ₁+τ₂, μ > 0`,
`W_quad(u_k, Δu) = 0`, and `inner_self_le_W_quad` then forces
`Δu = 0`, i.e., `v₁ = v₂`.

Note: the sphere hypothesis `u_k ∈ Sr` is not actually used — the
tangency clause in `IsRjnSolution` already supplies
`⟨u_k, v_i⟩ = 0`, which is the only sphere-related fact entering
the argument. It is kept in the signature to match paper
Proposition 11. -/
theorem IsRjnSolution.unique {μ : ℝ} (hμ : 0 < μ)
    {u_k : H X Y} (_hu_k_S : u_k ∈ 𝓢.sphere) (hu_k_C : u_k ∈ 𝓢.C_interior)
    {v₁ v₂ : H X Y}
    (h₁ : 𝓢.IsRjnSolution μ u_k v₁) (h₂ : 𝓢.IsRjnSolution μ u_k v₂) :
    v₁ = v₂ := by
  obtain ⟨h_tan_1, h_Cplus_1, θ₁, _hθ₁_pos, lam₁, h_newton_1, h_scalar_1⟩ := h₁
  obtain ⟨h_tan_2, h_Cplus_2, θ₂, _hθ₂_pos, lam₂, h_newton_2, h_scalar_2⟩ := h₂
  -- Vector abbreviations.
  set u₁ : H X Y := u_k + v₁ with hu₁_def
  set u₂ : H X Y := u_k + v₂ with hu₂_def
  set Δu : H X Y := u₁ - u₂ with hΔu_def
  -- Bridge: Δu = v₁ - v₂ (relies on defeq via the `set` bindings, so must
  -- be derived before `clear_value` below).
  have h_Δu_eq_v_diff : Δu = v₁ - v₂ := by
    show (u_k + v₁) - (u_k + v₂) = v₁ - v₂; abel
  -- Make `u₁, u₂, Δu` opaque so subsequent `rw` calls on
  -- `Px_bilinform_clm_add_*` don't peek through the `set`-bindings.
  clear_value u₁ u₂ Δu
  -- Scalar abbreviations.
  set τ₁ : ℝ := 𝓢.tau_proj u₁ with hτ₁_def
  set τ₂ : ℝ := 𝓢.tau_proj u₂ with hτ₂_def
  set τΔ : ℝ := 𝓢.tau_proj Δu with hτΔ_def
  set Px₁ : ℝ := 𝓢.Px_bilinform_clm u₁ u₁ with hPx₁_def
  set Px₂ : ℝ := 𝓢.Px_bilinform_clm u₂ u₂ with hPx₂_def
  set Px₁₂ : ℝ := 𝓢.Px_bilinform_clm u₁ u₂ with hPx₁₂_def
  set PxΔΔ : ℝ := 𝓢.Px_bilinform_clm Δu Δu with hPxΔΔ_def
  set PxUΔ : ℝ := 𝓢.Px_bilinform_clm (u₁ + u₂) Δu with hPxUΔ_def
  set PxUU : ℝ := 𝓢.Px_bilinform_clm (u₁ + u₂) (u₁ + u₂) with hPxUU_def
  set Wq : ℝ := 𝓢.W_quad u_k Δu with hWq_def
  -- Positivity / nonnegativity.
  have hτ₁_pos : 0 < τ₁ := 𝓢.tau_proj_pos h_Cplus_1
  have hτ₂_pos : 0 < τ₂ := 𝓢.tau_proj_pos h_Cplus_2
  have hT_pos : 0 < τ₁ + τ₂ := by linarith
  have hT_sq_pos : 0 < (τ₁ + τ₂) ^ 2 := by positivity
  have hτ₁τ₂_pos : 0 < τ₁ * τ₂ := mul_pos hτ₁_pos hτ₂_pos
  have hPx₁_nn : 0 ≤ Px₁ := 𝓢.Px_bilinform_self_nonneg _
  have hPx₂_nn : 0 ≤ Px₂ := 𝓢.Px_bilinform_self_nonneg _
  have hPxΔΔ_nn : 0 ≤ PxΔΔ := 𝓢.Px_bilinform_self_nonneg _
  have hWq_nn : 0 ≤ Wq := by
    have h := 𝓢.inner_self_le_W_quad u_k hu_k_C Δu
    linarith [@real_inner_self_nonneg _ _ _ Δu]
  -- Tangency ⟨u_k, Δu⟩ = 0 via the bridge.
  have h_tan_Δu : inner ℝ u_k Δu = (0 : ℝ) := by
    rw [h_Δu_eq_v_diff, inner_sub_right, h_tan_1, h_tan_2, sub_zero]
  -- Newton-equation difference: (H+M) Δu = (θ₁ - θ₂) e_τ - (λ₁ - λ₂) u_k.
  have h_newton_diff :
      (𝓢.hessian_h μ u_k + 𝓢.M_clm) Δu =
        (θ₁ - θ₂) • 𝓢.e_τ - (lam₁ - lam₂) • u_k := by
    rw [hΔu_def, map_sub, h_newton_1, h_newton_2]
    module
  -- ⟨Δu, (H+M) Δu⟩ = (θ₁ - θ₂) τΔ (tangency kills the λ-term).
  have h_inner_eq1 :
      inner ℝ Δu ((𝓢.hessian_h μ u_k + 𝓢.M_clm) Δu) = (θ₁ - θ₂) * τΔ := by
    rw [h_newton_diff, inner_sub_right, real_inner_smul_right,
        real_inner_smul_right, 𝓢.inner_u_e_tau]
    have h_inner_Δu_u_k : inner ℝ Δu u_k = (0 : ℝ) := by
      rw [real_inner_comm]; exact h_tan_Δu
    rw [h_inner_Δu_u_k, mul_zero, sub_zero]
  -- Structure identity: ⟨Δu, (H+M) Δu⟩ = μ Wq + PxΔΔ.
  have h_inner_expand :
      inner ℝ Δu ((𝓢.hessian_h μ u_k + 𝓢.M_clm) Δu) = μ * Wq + PxΔΔ := by
    rw [ContinuousLinearMap.add_apply, inner_add_right]
    congr 1
    · show inner ℝ Δu (μ • 𝓢.W_op u_k Δu) = μ * Wq
      rw [real_inner_smul_right, 𝓢.inner_self_W_op_eq_W_quad u_k hu_k_C]
    · exact 𝓢.inner_u_M Δu
  -- (♠): μ Wq + PxΔΔ = (θ₁ - θ₂) τΔ.
  have h_eq_W : μ * Wq + PxΔΔ = (θ₁ - θ₂) * τΔ := by
    rw [← h_inner_expand]; exact h_inner_eq1
  -- τΔ = τ₁ - τ₂ (linearity of tau_proj).
  have h_τΔ_eq : τΔ = τ₁ - τ₂ := by
    show 𝓢.tau_proj Δu = 𝓢.tau_proj u₁ - 𝓢.tau_proj u₂
    rw [hΔu_def]
    have h_sub : u₁ - u₂ = u₁ + (-1 : ℝ) • u₂ := by rw [neg_one_smul]; abel
    rw [h_sub, 𝓢.tau_proj_add, 𝓢.tau_proj_smul]; ring
  -- Px(U, Δu) = Px₁ - Px₂ via bilinearity + symmetry.
  have h_PxUΔ_eq : PxUΔ = Px₁ - Px₂ := by
    show 𝓢.Px_bilinform_clm (u₁ + u₂) Δu =
      𝓢.Px_bilinform_clm u₁ u₁ - 𝓢.Px_bilinform_clm u₂ u₂
    rw [hΔu_def]
    have h_sub : u₁ - u₂ = u₁ + (-1 : ℝ) • u₂ := by rw [neg_one_smul]; abel
    rw [h_sub, 𝓢.Px_bilinform_clm_add_left, 𝓢.Px_bilinform_clm_add_right,
        𝓢.Px_bilinform_clm_smul_right, 𝓢.Px_bilinform_clm_add_right,
        𝓢.Px_bilinform_clm_smul_right]
    have h_sym : 𝓢.Px_bilinform_clm u₂ u₁ = 𝓢.Px_bilinform_clm u₁ u₂ :=
      𝓢.Px_bilinform_clm_symm _ _
    linarith [h_sym]
  -- Px(U, U) = Px₁ + 2 Px₁₂ + Px₂.
  have h_PxUU_eq : PxUU = Px₁ + 2 * Px₁₂ + Px₂ := by
    show 𝓢.Px_bilinform_clm (u₁ + u₂) (u₁ + u₂) =
      𝓢.Px_bilinform_clm u₁ u₁ + 2 * 𝓢.Px_bilinform_clm u₁ u₂ + 𝓢.Px_bilinform_clm u₂ u₂
    rw [𝓢.Px_bilinform_clm_add_left, 𝓢.Px_bilinform_clm_add_right,
        𝓢.Px_bilinform_clm_add_right]
    have h_sym : 𝓢.Px_bilinform_clm u₂ u₁ = 𝓢.Px_bilinform_clm u₁ u₂ :=
      𝓢.Px_bilinform_clm_symm _ _
    linarith [h_sym]
  -- Scalar-equation difference: θ₁ τ₁ - θ₂ τ₂ = Px₁ - Px₂.
  have h_scalar_diff : θ₁ * τ₁ - θ₂ * τ₂ = Px₁ - Px₂ := by
    show θ₁ * 𝓢.tau_proj u₁ - θ₂ * 𝓢.tau_proj u₂
      = 𝓢.Px_bilinform_clm u₁ u₁ - 𝓢.Px_bilinform_clm u₂ u₂
    linarith [h_scalar_1, h_scalar_2]
  -- (♣): (θ₁-θ₂)(τ₁+τ₂) + (θ₁+θ₂) τΔ = 2 PxUΔ.
  have h_sum_eq :
      (θ₁ - θ₂) * (τ₁ + τ₂) + (θ₁ + θ₂) * τΔ = 2 * PxUΔ := by
    rw [h_τΔ_eq, h_PxUΔ_eq]
    linear_combination 2 * h_scalar_diff
  -- Multiply (♠) by T: (τ₁+τ₂) μ Wq + (τ₁+τ₂) PxΔΔ + (θ₁+θ₂) τΔ² = 2 τΔ PxUΔ.
  have h_main_eq :
      (τ₁ + τ₂) * (μ * Wq) + (τ₁ + τ₂) * PxΔΔ + (θ₁ + θ₂) * τΔ ^ 2
        = 2 * τΔ * PxUΔ := by
    linear_combination (τ₁ + τ₂) * h_eq_W + τΔ * h_sum_eq
  -- Multiply by T again.
  have h_main_eq' :
      (τ₁ + τ₂) ^ 2 * (μ * Wq) + (τ₁ + τ₂) ^ 2 * PxΔΔ
        + (τ₁ + τ₂) * (θ₁ + θ₂) * τΔ ^ 2 = 2 * (τ₁ + τ₂) * τΔ * PxUΔ := by
    linear_combination (τ₁ + τ₂) * h_main_eq
  -- PSD bound on (u₁+u₂, Δu, τ₁+τ₂, τΔ).
  have h_psd1 :
      2 * (τ₁ + τ₂) * τΔ * PxUΔ
        ≤ τΔ ^ 2 * PxUU + (τ₁ + τ₂) ^ 2 * PxΔΔ := by
    have h := 𝓢.Px_quad_form_psd
      (𝓢.x_proj (u₁ + u₂)) (𝓢.x_proj Δu) (τ₁ + τ₂) τΔ
    show 2 * (τ₁ + τ₂) * τΔ * 𝓢.Px_bilinform (𝓢.x_proj (u₁ + u₂)) (𝓢.x_proj Δu) ≤
      τΔ ^ 2 * 𝓢.Px_bilinform (𝓢.x_proj (u₁ + u₂)) (𝓢.x_proj (u₁ + u₂))
        + (τ₁ + τ₂) ^ 2 * 𝓢.Px_bilinform (𝓢.x_proj Δu) (𝓢.x_proj Δu)
    linarith [h]
  -- After PSD₁: (τ₁+τ₂)² μ Wq + (τ₁+τ₂)(θ₁+θ₂) τΔ² ≤ τΔ² PxUU.
  have h_after_psd1 :
      (τ₁ + τ₂) ^ 2 * (μ * Wq) + (τ₁ + τ₂) * (θ₁ + θ₂) * τΔ ^ 2
        ≤ τΔ ^ 2 * PxUU := by
    linarith [h_main_eq', h_psd1]
  -- PSD bound on (u₂, u₁, τ₂, τ₁) for the AM-GM step.
  have h_psd2 :
      2 * τ₁ * τ₂ * Px₁₂ ≤ τ₁ ^ 2 * Px₂ + τ₂ ^ 2 * Px₁ := by
    have h := 𝓢.Px_quad_form_psd (𝓢.x_proj u₂) (𝓢.x_proj u₁) τ₂ τ₁
    have h_sym :
        𝓢.Px_bilinform (𝓢.x_proj u₂) (𝓢.x_proj u₁) =
          𝓢.Px_bilinform (𝓢.x_proj u₁) (𝓢.x_proj u₂) :=
      𝓢.Px_bilinform_symm _ _
    rw [h_sym] at h
    show 2 * τ₁ * τ₂ * 𝓢.Px_bilinform (𝓢.x_proj u₁) (𝓢.x_proj u₂) ≤
      τ₁ ^ 2 * 𝓢.Px_bilinform (𝓢.x_proj u₂) (𝓢.x_proj u₂)
        + τ₂ ^ 2 * 𝓢.Px_bilinform (𝓢.x_proj u₁) (𝓢.x_proj u₁)
    linarith [h]
  -- Express Px_i via the scalar equations.
  have h_Px₁_eq : Px₁ = θ₁ * τ₁ - μ := by
    show 𝓢.Px_bilinform_clm u₁ u₁ = θ₁ * 𝓢.tau_proj u₁ - μ
    linarith [h_scalar_1]
  have h_Px₂_eq : Px₂ = θ₂ * τ₂ - μ := by
    show 𝓢.Px_bilinform_clm u₂ u₂ = θ₂ * 𝓢.tau_proj u₂ - μ
    linarith [h_scalar_2]
  -- AM-GM.
  have h_amgm : 2 * τ₁ * τ₂ ≤ τ₁ ^ 2 + τ₂ ^ 2 := by
    nlinarith [sq_nonneg (τ₁ - τ₂)]
  -- Key inequality: τ₁ θ₂ + τ₂ θ₁ - 2 Px₁₂ ≥ 2 μ.
  -- Multiply by τ₁ τ₂ > 0 and use h_psd2 + h_amgm.
  have h_pxbd : 2 * μ ≤ τ₁ * θ₂ + τ₂ * θ₁ - 2 * Px₁₂ := by
    -- Substitute Px_i = θ_i τ_i - μ in the PSD₂ bound to get a fully-distributed form.
    have h_distrib :
        2 * τ₁ * τ₂ * Px₁₂ ≤
          τ₁ ^ 2 * τ₂ * θ₂ + τ₂ ^ 2 * τ₁ * θ₁
            - μ * τ₁ ^ 2 - μ * τ₂ ^ 2 := by
      have h_sub :
          τ₁ ^ 2 * Px₂ + τ₂ ^ 2 * Px₁ =
            τ₁ ^ 2 * τ₂ * θ₂ + τ₂ ^ 2 * τ₁ * θ₁
              - μ * τ₁ ^ 2 - μ * τ₂ ^ 2 := by
        rw [h_Px₁_eq, h_Px₂_eq]; ring
      linarith [h_psd2, h_sub]
    -- AM-GM scaled: 2 μ τ₁ τ₂ ≤ μ τ₁² + μ τ₂².
    have h_amgm_scaled : 2 * μ * τ₁ * τ₂ ≤ μ * τ₁ ^ 2 + μ * τ₂ ^ 2 := by
      nlinarith [h_amgm, hμ.le]
    -- Add h_distrib and h_amgm_scaled to get the τ₁ τ₂-multiplied form of the goal.
    have h_cross :
        2 * μ * τ₁ * τ₂
          ≤ τ₁ ^ 2 * τ₂ * θ₂ + τ₂ ^ 2 * τ₁ * θ₁ - 2 * τ₁ * τ₂ * Px₁₂ := by
      linarith [h_distrib, h_amgm_scaled]
    -- Rewrite to the multiplied form and divide by τ₁ τ₂ > 0.
    have h_cross_mul :
        τ₁ * τ₂ * (2 * μ) ≤ τ₁ * τ₂ * (τ₁ * θ₂ + τ₂ * θ₁ - 2 * Px₁₂) := by
      have h_l : τ₁ * τ₂ * (2 * μ) = 2 * μ * τ₁ * τ₂ := by ring
      have h_r :
          τ₁ * τ₂ * (τ₁ * θ₂ + τ₂ * θ₁ - 2 * Px₁₂) =
            τ₁ ^ 2 * τ₂ * θ₂ + τ₂ ^ 2 * τ₁ * θ₁ - 2 * τ₁ * τ₂ * Px₁₂ := by ring
      rw [h_l, h_r]; exact h_cross
    exact le_of_mul_le_mul_left h_cross_mul hτ₁τ₂_pos
  -- PxUU ≤ T Θ - 4μ.
  have h_PxUU_bound : PxUU ≤ (τ₁ + τ₂) * (θ₁ + θ₂) - 4 * μ := by
    rw [h_PxUU_eq]
    nlinarith [h_Px₁_eq, h_Px₂_eq, h_pxbd]
  -- Multiply by τΔ² ≥ 0.
  have h_τΔ_PxUU_bound :
      τΔ ^ 2 * PxUU ≤ τΔ ^ 2 * ((τ₁ + τ₂) * (θ₁ + θ₂) - 4 * μ) :=
    mul_le_mul_of_nonneg_left h_PxUU_bound (sq_nonneg _)
  -- Combine: (τ₁+τ₂)² μ Wq + 4 μ τΔ² ≤ 0.
  have h_combined :
      (τ₁ + τ₂) ^ 2 * (μ * Wq) + 4 * μ * τΔ ^ 2 ≤ 0 := by
    have h_eq :
        τΔ ^ 2 * ((τ₁ + τ₂) * (θ₁ + θ₂) - 4 * μ) =
          (τ₁ + τ₂) * (θ₁ + θ₂) * τΔ ^ 2 - 4 * μ * τΔ ^ 2 := by ring
    linarith [h_after_psd1, h_τΔ_PxUU_bound, h_eq]
  -- Both summands non-negative ⟹ both zero ⟹ Wq = 0.
  have h_T_sq_μ_Wq_nn : 0 ≤ (τ₁ + τ₂) ^ 2 * (μ * Wq) :=
    mul_nonneg hT_sq_pos.le (mul_nonneg hμ.le hWq_nn)
  have h_μ_τΔ_sq_nn : 0 ≤ 4 * μ * τΔ ^ 2 := by positivity
  have h_T_sq_μ_Wq_zero : (τ₁ + τ₂) ^ 2 * (μ * Wq) = 0 := by linarith
  have h_μ_Wq_zero : μ * Wq = 0 :=
    (mul_eq_zero.mp h_T_sq_μ_Wq_zero).resolve_left (ne_of_gt hT_sq_pos)
  have h_Wq_zero : Wq = 0 :=
    (mul_eq_zero.mp h_μ_Wq_zero).resolve_left (ne_of_gt hμ)
  -- ‖Δu‖² ≤ Wq = 0 ⟹ Δu = 0.
  have h_inner_Δu_le : inner ℝ Δu Δu ≤ Wq :=
    𝓢.inner_self_le_W_quad u_k hu_k_C Δu
  rw [h_Wq_zero] at h_inner_Δu_le
  have h_inner_Δu_nn : (0 : ℝ) ≤ inner ℝ Δu Δu := real_inner_self_nonneg
  have h_inner_Δu_zero : inner ℝ Δu Δu = 0 :=
    le_antisymm h_inner_Δu_le h_inner_Δu_nn
  have h_norm_Δu_sq_zero : ‖Δu‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq]; exact h_inner_Δu_zero
  have h_norm_Δu_zero : ‖Δu‖ = 0 :=
    pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h_norm_Δu_sq_zero
  have h_Δu_zero : Δu = 0 := norm_eq_zero.mp h_norm_Δu_zero
  -- Conclude v₁ = v₂.
  have h_v_diff_zero : v₁ - v₂ = 0 := by
    rw [← h_Δu_eq_v_diff]; exact h_Δu_zero
  exact sub_eq_zero.mp h_v_diff_zero

/-! ### Implicit function theorem setup for the RJN system

The proofs of `rjnDirection_locallyLipschitz` and (with one extra
Newton-identity step) `rjnDirection_tangent_step_quadratic_bound`
both reduce to a single application of Mathlib's implicit function
theorem to the joint RJN system
`G(u_k, v, λ, θ) = (Newton, tangency, scalar)`. The IFT gives a
smooth implicit function `ψ : nhd u*(μ) → H × ℝ × ℝ` with
`ψ(u*) = (0, 0, θ*)`; the global uniqueness lemma
`IsRjnSolution.unique` then identifies `(ψ u_k).1` with
`rjnDirection μ u_k` in a neighbourhood (without needing the
IFT-branch uniqueness side-condition).

This section sets up the algebraic core: a positive lower bound on
the "discriminant" `θ* Px(w,w) - 2 Px(u*, w) + τ*` that appears when
inverting the partial Jacobian of `G` at the basepoint
`(u*, 0, 0, θ*)`. -/

/-- **Discriminant positivity at the central path** (algebraic core of
the IFT invertibility). For every `w : H X Y`,
`θ* · Px(w, w) - 2 Px(u*, w) + τ* ≥ μ / θ* > 0`, where
`u* = centralPathPoint μ hμ`, `θ* = (Px(u*, u*) + μ) / τ(u*)`, and
`Px`, `τ` are the primal bilinear form and τ-projection.

This scalar is the determinant of the `(δλ, δθ)`-block of the
partial Jacobian of the RJN system at `(u*, 0, 0, θ*)` (after
reducing through tangency); its positivity is exactly the
non-degeneracy condition that the implicit function theorem requires.

**Proof.** Apply `Px_quad_form_psd` with `(τu, τv) = (θ*, 1)` and
`(xu, xv) = (x_proj u*, x_proj w)`:
```
  0 ≤ Px(u*, u*) - 2 θ* Px(u*, w) + θ*² Px(w, w).
```
Hence `2 θ* Px(u*, w) - θ*² Px(w, w) ≤ Px*`. Subtract from
`θ* τ* = Px* + μ`:
```
  θ* τ* - 2 θ* Px(u*, w) + θ*² Px(w, w) ≥ Px* + μ - Px* = μ.
```
Factor `θ*` from the LHS and divide by `θ* > 0`. -/
theorem rjn_discriminant_ge_mu_div_θ {μ : ℝ} (hμ : 0 < μ) (w : H X Y) :
    μ / ((𝓢.Px_bilinform_clm (𝓢.centralPathPoint μ hμ)
              (𝓢.centralPathPoint μ hμ) + μ)
        / 𝓢.tau_proj (𝓢.centralPathPoint μ hμ)) ≤
      (𝓢.Px_bilinform_clm (𝓢.centralPathPoint μ hμ)
            (𝓢.centralPathPoint μ hμ) + μ)
          / 𝓢.tau_proj (𝓢.centralPathPoint μ hμ)
        * 𝓢.Px_bilinform_clm w w
      - 2 * 𝓢.Px_bilinform_clm (𝓢.centralPathPoint μ hμ) w
      + 𝓢.tau_proj (𝓢.centralPathPoint μ hμ) := by
  set u_star := 𝓢.centralPathPoint μ hμ with hu_star_def
  obtain ⟨hC_star, _⟩ := 𝓢.centralPathPoint_isCentralPathPoint μ hμ
  have hu_star_Cplus : u_star ∈ 𝓢.Cplus := 𝓢.C_interior_subset_Cplus hC_star
  have hτ_pos : 0 < 𝓢.tau_proj u_star := 𝓢.tau_proj_pos hu_star_Cplus
  have hPx_clm_apply :
      𝓢.Px_bilinform_clm u_star u_star =
        𝓢.Px_bilinform (𝓢.x_proj u_star) (𝓢.x_proj u_star) := rfl
  have hPx_uw_clm_apply :
      𝓢.Px_bilinform_clm u_star w =
        𝓢.Px_bilinform (𝓢.x_proj u_star) (𝓢.x_proj w) := rfl
  have hPx_ww_clm_apply :
      𝓢.Px_bilinform_clm w w =
        𝓢.Px_bilinform (𝓢.x_proj w) (𝓢.x_proj w) := rfl
  set Px_star := 𝓢.Px_bilinform_clm u_star u_star with hPx_star_def
  have hPx_star_nn : 0 ≤ Px_star := by
    rw [hPx_clm_apply]; exact 𝓢.Px_bilinform_self_nonneg _
  set τ_star := 𝓢.tau_proj u_star with hτ_star_def
  set θ_star : ℝ := (Px_star + μ) / τ_star with hθ_def
  have hθ_pos : 0 < θ_star := div_pos (by linarith) hτ_pos
  have hθ_τ : θ_star * τ_star = Px_star + μ := by
    rw [hθ_def]; field_simp
  -- PSD: 0 ≤ Px* - 2 θ* Px(u*, w) + θ*² Px(w, w).
  have h_psd_raw :=
    𝓢.Px_quad_form_psd (𝓢.x_proj u_star) (𝓢.x_proj w) θ_star 1
  have h_psd : 0 ≤ Px_star - 2 * θ_star * 𝓢.Px_bilinform_clm u_star w
        + θ_star ^ 2 * 𝓢.Px_bilinform_clm w w := by
    rw [hPx_clm_apply, hPx_uw_clm_apply, hPx_ww_clm_apply]
    nlinarith [h_psd_raw]
  -- Multiply target by θ_star: get θ_star * (target) ≥ μ.
  have h_main :
      μ ≤ θ_star * (θ_star * 𝓢.Px_bilinform_clm w w
              - 2 * 𝓢.Px_bilinform_clm u_star w + τ_star) := by
    have h_alg : θ_star * (θ_star * 𝓢.Px_bilinform_clm w w
                    - 2 * 𝓢.Px_bilinform_clm u_star w + τ_star)
               = θ_star ^ 2 * 𝓢.Px_bilinform_clm w w
                 - 2 * θ_star * 𝓢.Px_bilinform_clm u_star w
                 + θ_star * τ_star := by ring
    rw [h_alg, hθ_τ]
    linarith
  -- Divide by θ_star > 0.
  rw [div_le_iff₀ hθ_pos]
  linarith

/-- Strict positivity corollary of `rjn_discriminant_ge_mu_div_θ`. -/
theorem rjn_discriminant_pos {μ : ℝ} (hμ : 0 < μ) (w : H X Y) :
    0 < (𝓢.Px_bilinform_clm (𝓢.centralPathPoint μ hμ)
              (𝓢.centralPathPoint μ hμ) + μ)
          / 𝓢.tau_proj (𝓢.centralPathPoint μ hμ)
        * 𝓢.Px_bilinform_clm w w
      - 2 * 𝓢.Px_bilinform_clm (𝓢.centralPathPoint μ hμ) w
      + 𝓢.tau_proj (𝓢.centralPathPoint μ hμ) := by
  set u_star := 𝓢.centralPathPoint μ hμ with hu_star_def
  obtain ⟨hC_star, _⟩ := 𝓢.centralPathPoint_isCentralPathPoint μ hμ
  have hu_star_Cplus : u_star ∈ 𝓢.Cplus := 𝓢.C_interior_subset_Cplus hC_star
  have hτ_pos : 0 < 𝓢.tau_proj u_star := 𝓢.tau_proj_pos hu_star_Cplus
  have hPx_star_nn : 0 ≤ 𝓢.Px_bilinform_clm u_star u_star := by
    show 0 ≤ 𝓢.Px_bilinform (𝓢.x_proj u_star) (𝓢.x_proj u_star)
    exact 𝓢.Px_bilinform_self_nonneg _
  have hθ_pos : 0 < (𝓢.Px_bilinform_clm u_star u_star + μ) / 𝓢.tau_proj u_star :=
    div_pos (by linarith) hτ_pos
  have h_div_pos : 0 < μ / ((𝓢.Px_bilinform_clm u_star u_star + μ)
      / 𝓢.tau_proj u_star) := div_pos hμ hθ_pos
  linarith [𝓢.rjn_discriminant_ge_mu_div_θ hμ w]

set_option maxHeartbeats 800000 in
/-- **Kernel triviality of the partial Jacobian at the central-path
basepoint.** Suppose `(dv, dlam, dth) ∈ H × ℝ × ℝ` satisfies the
linearised RJN system at `(u*, 0, 0, θ*)`:
* `(H + M) dv = dth • e_τ - dlam • u*` (Newton),
* `⟨u*, dv⟩ = 0` (tangency),
* `τ* dth + θ* τ(dv) - 2 Px(u*, dv) = 0` (scalar),

where `u* = centralPathPoint μ hμ`, `τ* = τ(u*)`, `Px* = Px(u*, u*)`,
`θ* = (Px* + μ)/τ*`. Then `dv = 0`, `dlam = 0`, `dth = 0`.

**Proof.** Inner-product the Newton equation with `dv` and use the
tangency `⟨u*, dv⟩ = 0`: `⟨dv, (H+M) dv⟩ = dth · τ(dv)`. By the
operator structure, `⟨dv, (H+M) dv⟩ = μ W_quad(u*, dv) + Px(dv, dv)`,
hence `dth τ(dv) = μ W_quad(u*, dv) + Px(dv, dv)`. Multiply by `τ*`
and substitute `τ* dth = 2 Px(u*, dv) - θ* τ(dv)` (from the scalar
equation):
```
  τ*² μ W_quad + τ*² Px(dv, dv) + (Px* + μ) τ(dv)²
    = 2 τ* τ(dv) Px(u*, dv).
```
The PSD bound (`Px_quad_form_psd` with `(τu, τv) = (τ*, τ(dv))`)
gives `2 τ* τ(dv) Px(u*, dv) ≤ τ(dv)² Px* + τ*² Px(dv, dv)`.
Subtracting:
```
  τ*² μ W_quad(u*, dv) + μ τ(dv)² ≤ 0.
```
All four factors are non-negative, forcing `W_quad(u*, dv) = 0`. Since
`W_quad(u*, v) ≥ ‖v‖²`, this gives `dv = 0`. Then the scalar
equation at `dv = 0` reduces to `τ* dth = 0`, hence `dth = 0` (`τ* > 0`).
Finally the Newton equation at `(dv, dth) = (0, 0)` reduces to
`-dlam u* = 0`, hence `dlam = 0` (since `‖u*‖² = ν+1 > 0`). -/
theorem rjn_partial_jacobian_kernel_trivial {μ : ℝ} (hμ : 0 < μ)
    {dv : H X Y} {dlam dth : ℝ}
    (h_eq1 : (𝓢.hessian_h μ (𝓢.centralPathPoint μ hμ) + 𝓢.M_clm) dv
              = dth • 𝓢.e_τ - dlam • 𝓢.centralPathPoint μ hμ)
    (h_eq2 : inner ℝ (𝓢.centralPathPoint μ hμ) dv = (0 : ℝ))
    (h_eq3 : 𝓢.tau_proj (𝓢.centralPathPoint μ hμ) * dth
              + ((𝓢.Px_bilinform_clm (𝓢.centralPathPoint μ hμ)
                    (𝓢.centralPathPoint μ hμ) + μ)
                  / 𝓢.tau_proj (𝓢.centralPathPoint μ hμ))
                * 𝓢.tau_proj dv
              - 2 * 𝓢.Px_bilinform_clm (𝓢.centralPathPoint μ hμ) dv
              = 0) :
    dv = 0 ∧ dlam = 0 ∧ dth = 0 := by
  set u_star := 𝓢.centralPathPoint μ hμ with hu_star_def
  obtain ⟨hC_star, hT_star⟩ := 𝓢.centralPathPoint_isCentralPathPoint μ hμ
  have hu_star_Cplus : u_star ∈ 𝓢.Cplus := 𝓢.C_interior_subset_Cplus hC_star
  have hτ_pos : 0 < 𝓢.tau_proj u_star := 𝓢.tau_proj_pos hu_star_Cplus
  have hτ_ne : 𝓢.tau_proj u_star ≠ 0 := ne_of_gt hτ_pos
  have hu_star_norm_sq : ‖u_star‖ ^ 2 = (𝓢.ν : ℝ) + 1 :=
    𝓢.centralPath_norm_sq hμ ⟨hC_star, hT_star⟩
  have hu_star_norm_sq_pos : 0 < ‖u_star‖ ^ 2 := by
    rw [hu_star_norm_sq]
    have : (0 : ℝ) ≤ (𝓢.ν : ℝ) := Nat.cast_nonneg _
    linarith
  have hPx_star_nn : 0 ≤ 𝓢.Px_bilinform_clm u_star u_star := by
    show 0 ≤ 𝓢.Px_bilinform (𝓢.x_proj u_star) (𝓢.x_proj u_star)
    exact 𝓢.Px_bilinform_self_nonneg _
  set τ_star := 𝓢.tau_proj u_star with hτ_star_def
  set Px_star := 𝓢.Px_bilinform_clm u_star u_star with hPx_star_def
  set θ_star : ℝ := (Px_star + μ) / τ_star with hθ_star_def
  have hθ_τ : θ_star * τ_star = Px_star + μ := by
    rw [hθ_star_def]; field_simp
  -- Step 1: ⟨dv, (H+M) dv⟩ = dth τ(dv) using tangency ⟨u*, dv⟩ = 0.
  have h_inner_eq1 :
      inner ℝ dv ((𝓢.hessian_h μ u_star + 𝓢.M_clm) dv)
        = dth * 𝓢.tau_proj dv := by
    rw [h_eq1]
    rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right,
        𝓢.inner_u_e_tau]
    have h_dv_u_star : inner ℝ dv u_star = (0 : ℝ) := by
      rw [real_inner_comm]; exact h_eq2
    rw [h_dv_u_star]; ring
  -- Operator-structure identity: ⟨dv, (H+M) dv⟩ = μ W_quad + Px(dv, dv).
  have h_inner_expand :
      inner ℝ dv ((𝓢.hessian_h μ u_star + 𝓢.M_clm) dv)
        = μ * 𝓢.W_quad u_star dv + 𝓢.Px_bilinform_clm dv dv := by
    show inner ℝ dv (𝓢.hessian_h μ u_star dv + 𝓢.M_clm dv) = _
    rw [inner_add_right]
    congr 1
    · show inner ℝ dv (μ • 𝓢.W_op u_star dv) = μ * 𝓢.W_quad u_star dv
      rw [real_inner_smul_right, 𝓢.inner_self_W_op_eq_W_quad u_star hC_star]
    · show inner ℝ dv (𝓢.M_apply dv) = _
      rw [𝓢.inner_u_M]; rfl
  have h_key1 :
      dth * 𝓢.tau_proj dv =
        μ * 𝓢.W_quad u_star dv + 𝓢.Px_bilinform_clm dv dv := by
    rw [← h_inner_eq1, h_inner_expand]
  -- Step 2: τ* dth = 2 Px(u*, dv) - θ* τ(dv) from scalar eq.
  have h_key2 :
      τ_star * dth =
        2 * 𝓢.Px_bilinform_clm u_star dv - θ_star * 𝓢.tau_proj dv := by
    linarith [h_eq3]
  -- Multiply h_key1 by τ* and substitute h_key2:
  -- τ*² μ W_quad + τ*² Px(dv, dv) + (Px* + μ) τ(dv)² = 2 τ* τ(dv) Px(u*, dv).
  have h_multby_τ :
      τ_star ^ 2 * (μ * 𝓢.W_quad u_star dv)
        + τ_star ^ 2 * 𝓢.Px_bilinform_clm dv dv
        + (Px_star + μ) * 𝓢.tau_proj dv ^ 2
        = 2 * τ_star * 𝓢.tau_proj dv * 𝓢.Px_bilinform_clm u_star dv := by
    have h_τkey1 : τ_star * (dth * 𝓢.tau_proj dv)
        = τ_star * (μ * 𝓢.W_quad u_star dv + 𝓢.Px_bilinform_clm dv dv) := by
      rw [h_key1]
    have h_assoc : τ_star * (dth * 𝓢.tau_proj dv) = (τ_star * dth) * 𝓢.tau_proj dv := by
      ring
    rw [h_assoc, h_key2] at h_τkey1
    nlinarith [h_τkey1, hθ_τ, sq_nonneg τ_star, sq_nonneg (𝓢.tau_proj dv)]
  -- PSD: 0 ≤ τ(dv)² Px* - 2 τ* τ(dv) Px(u*, dv) + τ*² Px(dv, dv).
  have h_psd_raw :=
    𝓢.Px_quad_form_psd (𝓢.x_proj u_star) (𝓢.x_proj dv) τ_star (𝓢.tau_proj dv)
  have h_psd' :
      2 * τ_star * 𝓢.tau_proj dv * 𝓢.Px_bilinform_clm u_star dv ≤
        𝓢.tau_proj dv ^ 2 * Px_star + τ_star ^ 2 * 𝓢.Px_bilinform_clm dv dv := by
    have h_e1 : 𝓢.Px_bilinform (𝓢.x_proj u_star) (𝓢.x_proj u_star) = Px_star := rfl
    have h_e2 : 𝓢.Px_bilinform (𝓢.x_proj u_star) (𝓢.x_proj dv) =
                  𝓢.Px_bilinform_clm u_star dv := rfl
    have h_e3 : 𝓢.Px_bilinform (𝓢.x_proj dv) (𝓢.x_proj dv) =
                  𝓢.Px_bilinform_clm dv dv := rfl
    rw [h_e1, h_e2, h_e3] at h_psd_raw
    linarith [h_psd_raw]
  -- Combine: τ*² μ W_quad + μ τ(dv)² ≤ 0.
  have h_W_quad_nn : 0 ≤ 𝓢.W_quad u_star dv := by
    have h := 𝓢.inner_self_le_W_quad u_star hC_star dv
    linarith [@real_inner_self_nonneg _ _ _ dv]
  have h_Px_dv_nn : 0 ≤ 𝓢.Px_bilinform_clm dv dv := by
    show 0 ≤ 𝓢.Px_bilinform (𝓢.x_proj dv) (𝓢.x_proj dv)
    exact 𝓢.Px_bilinform_self_nonneg _
  have h_final_ineq :
      τ_star ^ 2 * (μ * 𝓢.W_quad u_star dv) + μ * 𝓢.tau_proj dv ^ 2 ≤ 0 := by
    nlinarith [h_multby_τ, h_psd', hPx_star_nn, sq_nonneg τ_star]
  -- Both terms in LHS non-negative, so both = 0.
  have hτ_star_sq_pos : 0 < τ_star ^ 2 := by positivity
  have h_W_quad_zero : 𝓢.W_quad u_star dv = 0 := by
    have h1 : 0 ≤ τ_star ^ 2 * (μ * 𝓢.W_quad u_star dv) :=
      mul_nonneg hτ_star_sq_pos.le (mul_nonneg hμ.le h_W_quad_nn)
    have h2 : 0 ≤ μ * 𝓢.tau_proj dv ^ 2 :=
      mul_nonneg hμ.le (sq_nonneg _)
    have h_sum_zero : τ_star ^ 2 * (μ * 𝓢.W_quad u_star dv)
                      + μ * 𝓢.tau_proj dv ^ 2 = 0 := by linarith
    have h_first_zero : τ_star ^ 2 * (μ * 𝓢.W_quad u_star dv) = 0 := by linarith
    have h_μWQ_zero : μ * 𝓢.W_quad u_star dv = 0 :=
      (mul_eq_zero.mp h_first_zero).resolve_left (ne_of_gt hτ_star_sq_pos)
    exact (mul_eq_zero.mp h_μWQ_zero).resolve_left (ne_of_gt hμ)
  -- ‖dv‖² ≤ W_quad = 0, hence dv = 0.
  have h_dv_zero : dv = 0 := by
    have h_inner_le : inner ℝ dv dv ≤ 𝓢.W_quad u_star dv :=
      𝓢.inner_self_le_W_quad u_star hC_star dv
    rw [h_W_quad_zero] at h_inner_le
    have h_inner_nn : (0 : ℝ) ≤ inner ℝ dv dv := real_inner_self_nonneg
    have h_inner_zero : inner ℝ dv dv = 0 := le_antisymm h_inner_le h_inner_nn
    have h_norm_sq_zero : ‖dv‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq]; exact h_inner_zero
    have h_norm_zero : ‖dv‖ = 0 :=
      pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0) |>.mp h_norm_sq_zero
    exact norm_eq_zero.mp h_norm_zero
  -- dth = 0 from scalar eq with dv = 0.
  have h_dth_zero : dth = 0 := by
    have h := h_eq3
    rw [h_dv_zero] at h
    have h_tau_zero : 𝓢.tau_proj (0 : H X Y) = 0 := by
      show (0 : H X Y).snd.snd = 0; rfl
    have hPx_uv_zero : 𝓢.Px_bilinform_clm u_star (0 : H X Y) = 0 := by
      show 𝓢.Px_bilinform (𝓢.x_proj u_star) (𝓢.x_proj (0 : H X Y)) = 0
      have h_xproj_zero : 𝓢.x_proj (0 : H X Y) = 0 := by
        show (0 : H X Y).fst = 0; rfl
      rw [h_xproj_zero]
      show inner ℝ (𝓢.x_proj u_star) (𝓢.P (0 : X)) = 0
      rw [map_zero, inner_zero_right]
    rw [h_tau_zero, mul_zero, add_zero, hPx_uv_zero, mul_zero, sub_zero] at h
    exact (mul_eq_zero.mp h).resolve_left hτ_ne
  -- dlam = 0 from Newton eq with dv = 0, dth = 0.
  have h_dlam_zero : dlam = 0 := by
    have h := h_eq1
    rw [h_dv_zero, h_dth_zero] at h
    simp only [map_zero, zero_smul, zero_sub] at h
    -- h : 0 = -(dlam • u_star), i.e., dlam • u_star = 0.
    have h_smul_eq : dlam • u_star = 0 := neg_eq_zero.mp h.symm
    -- Take inner product with u_star: dlam ‖u_star‖² = 0.
    have h_inner_smul :
        inner ℝ u_star (dlam • u_star) = dlam * inner ℝ u_star u_star := by
      rw [real_inner_smul_right]
    have h_inner_zero : inner ℝ u_star (dlam • u_star) = 0 := by
      rw [h_smul_eq, inner_zero_right]
    have h_inner_eq : dlam * inner ℝ u_star u_star = 0 := by
      rw [← h_inner_smul]; exact h_inner_zero
    rw [real_inner_self_eq_norm_sq] at h_inner_eq
    exact (mul_eq_zero.mp h_inner_eq).resolve_right (ne_of_gt hu_star_norm_sq_pos)
  exact ⟨h_dv_zero, h_dlam_zero, h_dth_zero⟩

/-! ### Joint smoothness of the RJN system

We package the three RJN residuals into a single function `rjnSystem`
and prove it is `C¹` jointly at the central-path basepoint
`(u*, 0, 0, θ*)`. The smoothness is limited by `hess_op`, which is
`C^(d-2)` in its argument: `F_lhscb.f` is `C^d`, its first derivative
is `C^(d-1)`, and the second derivative is `C^(d-2)`. With the
running hypothesis `d ≥ 3`, this is at least `C¹` — enough to apply
Mathlib's implicit function theorem. For the quadratic-bound lemma
(`rjnDirection_tangent_step_quadratic_bound`) `C²` of the implicit
function is needed, which requires `d ≥ 4`; that gap is documented
in the corresponding sorry. -/

/-- `hess_op` evaluated bilinearly: `(u, v) ↦ hess_op u v` is `C¹` at
any `(u₀, v₀)` with `u₀ ∈ C_interior`. Two derivatives of `F_lhscb.f`
(`C^d` with `d ≥ 3`) make the bilinear application `C¹`.

**Sorry — Mathlib instance-synthesis gap.** The natural proof chain
`F.f ∈ C³` ⟹ `fderiv F.f ∈ C²` ⟹ `fderiv (fderiv F.f) ∈ C¹` runs into
a typeclass-synthesis failure at the second step: Lean cannot
synthesize `NormedAddCommGroup (H X Y →L[ℝ] H X Y →L[ℝ] ℝ)` —
i.e. the iterated CLM codomain. Mathlib's
`ContinuousLinearMap.toNormedAddCommGroup` should apply recursively
but the abbrev unfolding of `H X Y = WithLp 2 (X × WithLp 2 (Y × ℝ))`
seems to block it at this depth.

Workarounds to try:
* Route through `iteratedFDerivWithin 2 F.f` (codomain
  `ContinuousMultilinearMap`, different instance setup) and convert
  via `continuousMultilinearCurryLeftEquiv` at the end.
* Provide a custom `NormedAddCommGroup` instance for the iterated
  CLM type directly in the file's preamble.
* Reformulate the RJN Newton-equation residual to avoid the
  operator-valued Hessian (e.g., using `hessianBilin` scalars
  paired with Riesz), so the smoothness proof never goes through
  the iterated CLM. -/
private lemma hess_op_apply_contDiffAt
    {u₀ : H X Y} (hu₀ : u₀ ∈ 𝓢.C_interior) (v₀ : H X Y) :
    ContDiffAt ℝ 1 (fun p : H X Y × H X Y => 𝓢.hess_op p.1 p.2) (u₀, v₀) := by
  sorry

/-- **The joint RJN system.** Bundles the three RJN residuals (Newton,
tangency, scalar) into a single function
`H × (H × ℝ × ℝ) → H × ℝ × ℝ` whose zero set is the
`IsRjnSolution`-locus (modulo the inequality constraints `θ > 0`,
`u_k + v ∈ Cplus`, which are open and preserved under IFT).

Layout of `p : H × (H × ℝ × ℝ)`:
* `p.1 = u_k`
* `p.2.1 = v`
* `p.2.2.1 = lam`
* `p.2.2.2 = th` -/
noncomputable def rjnSystem (𝓢 : IrnSetup X Y) (μ : ℝ) :
    H X Y × (H X Y × ℝ × ℝ) → H X Y × ℝ × ℝ :=
  fun p =>
    ((𝓢.hessian_h μ p.1 + 𝓢.M_clm) (p.1 + p.2.1)
      - 𝓢.hessian_h μ p.1 p.1
      + (μ • p.1 + μ • 𝓢.f_lhscb.grad p.1 + p.2.2.1 • p.1)
      - p.2.2.2 • 𝓢.e_τ,
     inner ℝ p.1 p.2.1,
     p.2.2.2 * 𝓢.tau_proj (p.1 + p.2.1)
       - 𝓢.Px_bilinform_clm (p.1 + p.2.1) (p.1 + p.2.1) - μ)

set_option maxHeartbeats 800000 in
/-- **Joint smoothness of the RJN system at the central-path basepoint.**
`rjnSystem μ` is `C¹` at `(u*, (0, 0, θ*))`.

The Newton-residual component combines:
* `μ • v` (`C^∞`),
* `μ • hess_op u_k v` (`C¹` by `hess_op_apply_contDiffAt`),
* `M_clm` applied to `u_k + v` (`C^∞`, linear),
* `μ • u_k + μ • ∇F*(u_k) + lam • u_k - θ • e_τ`
  (`C^(d-1) ≥ C¹` via `f_lhscb_grad_contDiffAt` and bilinear smul).

The tangency residual `⟨u_k, v⟩` is `C^∞` (bilinear inner product).

The scalar residual `θ τ(u_k + v) - Px(u_k+v, u_k+v) - μ` is `C^∞`
(bilinear/quadratic in linear projections and `θ`).

The least-smooth piece is the `hess_op` part, so the joint
smoothness class drops to `C¹` — which is the threshold the IFT
needs anyway. -/
theorem rjnSystem_contDiffAt {μ : ℝ} (hμ : 0 < μ) :
    ContDiffAt ℝ 1 (𝓢.rjnSystem μ)
      (𝓢.centralPathPoint μ hμ,
        (0, 0, ((𝓢.Px_bilinform_clm (𝓢.centralPathPoint μ hμ)
                  (𝓢.centralPathPoint μ hμ) + μ)
              / 𝓢.tau_proj (𝓢.centralPathPoint μ hμ)))) := by
  set u_star := 𝓢.centralPathPoint μ hμ with hu_star_def
  obtain ⟨hC_star, _⟩ := 𝓢.centralPathPoint_isCentralPathPoint μ hμ
  set basepoint :
      H X Y × (H X Y × ℝ × ℝ) :=
    (u_star, (0, 0, ((𝓢.Px_bilinform_clm u_star u_star + μ)
                      / 𝓢.tau_proj u_star)))
  -- Common projections.
  have h_fst : ContDiffAt ℝ 1 (Prod.fst :
      H X Y × (H X Y × ℝ × ℝ) → H X Y) basepoint := contDiffAt_fst
  have h_snd : ContDiffAt ℝ 1 (Prod.snd :
      H X Y × (H X Y × ℝ × ℝ) → H X Y × ℝ × ℝ) basepoint := contDiffAt_snd
  -- u_k = p.1 is C^∞ in p.
  have h_uk : ContDiffAt ℝ 1
      (fun p : H X Y × (H X Y × ℝ × ℝ) => p.1) basepoint := h_fst
  -- v = p.2.1 is C^∞ in p.
  have h_v : ContDiffAt ℝ 1
      (fun p : H X Y × (H X Y × ℝ × ℝ) => p.2.1) basepoint :=
    contDiffAt_fst.fun_comp _ h_snd
  -- lam = p.2.2.1 is C^∞ in p.
  have h_lam : ContDiffAt ℝ 1
      (fun p : H X Y × (H X Y × ℝ × ℝ) => p.2.2.1) basepoint :=
    contDiffAt_fst.fun_comp _ (contDiffAt_snd.fun_comp _ h_snd)
  -- th = p.2.2.2 is C^∞ in p.
  have h_th : ContDiffAt ℝ 1
      (fun p : H X Y × (H X Y × ℝ × ℝ) => p.2.2.2) basepoint :=
    contDiffAt_snd.fun_comp _ (contDiffAt_snd.fun_comp _ h_snd)
  -- u_k + v is C^∞ jointly.
  have h_uk_v : ContDiffAt ℝ 1
      (fun p : H X Y × (H X Y × ℝ × ℝ) => p.1 + p.2.1) basepoint :=
    h_uk.add h_v
  -- f_lhscb.grad u_k is C^(d-1) at u_star ∈ C_interior, hence C^1.
  have h_grad_at_uk : ContDiffAt ℝ (𝓢.d - 1) 𝓢.f_lhscb.grad u_star :=
    𝓢.f_lhscb_grad_contDiffAt (𝓢.C_interior_subset_f_lhscb_interior hC_star)
  have h_d1_ge : (1 : WithTop ℕ∞) ≤ ((𝓢.d - 1 : ℕ∞) : WithTop ℕ∞) := by
    have h : (2 : ℕ∞) ≤ 𝓢.d := le_trans (by decide) 𝓢.hd_ge
    have hcalc : (1 : ℕ∞) ≤ 𝓢.d - 1 := by
      calc (1 : ℕ∞) = 2 - 1 := by decide
        _ ≤ 𝓢.d - 1 := tsub_le_tsub_right h 1
    exact_mod_cast hcalc
  have h_grad_C1 : ContDiffAt ℝ 1 𝓢.f_lhscb.grad u_star :=
    h_grad_at_uk.of_le h_d1_ge
  have h_grad_pcomp : ContDiffAt ℝ 1
      (fun p : H X Y × (H X Y × ℝ × ℝ) => 𝓢.f_lhscb.grad p.1) basepoint :=
    h_grad_C1.fun_comp _ h_uk
  -- M_clm (u_k + v) is C^∞ jointly (linear).
  have h_M_clm : ContDiffAt ℝ 1
      (fun p : H X Y × (H X Y × ℝ × ℝ) => 𝓢.M_clm (p.1 + p.2.1)) basepoint :=
    𝓢.M_clm.contDiff.contDiffAt.fun_comp _ h_uk_v
  -- hess_op u_k applied to (u_k + v): via comp₂ with f₁ = .1, f₂ = + .
  have h_hess_uk_v : ContDiffAt ℝ 1
      (fun p : H X Y × (H X Y × ℝ × ℝ) => 𝓢.hess_op p.1 (p.1 + p.2.1)) basepoint := by
    have h := 𝓢.hess_op_apply_contDiffAt hC_star (u_star + 0)
    -- The basepoint of h is (u_star, u_star + 0) = (basepoint.1, basepoint.1 + basepoint.2.1).
    exact h.comp₂ h_uk h_uk_v
  -- Similarly hess_op u_k u_k.
  have h_hess_uk_uk : ContDiffAt ℝ 1
      (fun p : H X Y × (H X Y × ℝ × ℝ) => 𝓢.hess_op p.1 p.1) basepoint := by
    have h := 𝓢.hess_op_apply_contDiffAt hC_star u_star
    exact h.comp₂ h_uk h_uk
  -- hessian_h μ p.1 applied to (p.1 + p.2.1) = μ • (p.1 + p.2.1) + μ • hess_op p.1 (p.1 + p.2.1).
  have h_H_uk_v : ContDiffAt ℝ 1
      (fun p : H X Y × (H X Y × ℝ × ℝ) =>
        𝓢.hessian_h μ p.1 (p.1 + p.2.1)) basepoint := by
    show ContDiffAt ℝ 1
      (fun p : H X Y × (H X Y × ℝ × ℝ) =>
        μ • 𝓢.W_op p.1 (p.1 + p.2.1)) basepoint
    show ContDiffAt ℝ 1
      (fun p : H X Y × (H X Y × ℝ × ℝ) =>
        μ • ((p.1 + p.2.1) + 𝓢.hess_op p.1 (p.1 + p.2.1))) basepoint
    refine (h_uk_v.add h_hess_uk_v).const_smul μ
  have h_H_uk_uk : ContDiffAt ℝ 1
      (fun p : H X Y × (H X Y × ℝ × ℝ) =>
        𝓢.hessian_h μ p.1 p.1) basepoint := by
    show ContDiffAt ℝ 1
      (fun p : H X Y × (H X Y × ℝ × ℝ) =>
        μ • (p.1 + 𝓢.hess_op p.1 p.1)) basepoint
    refine (h_uk.add h_hess_uk_uk).const_smul μ
  -- Newton residual is C^1.
  have h_newton : ContDiffAt ℝ 1
      (fun p : H X Y × (H X Y × ℝ × ℝ) =>
        (𝓢.hessian_h μ p.1 + 𝓢.M_clm) (p.1 + p.2.1)
          - 𝓢.hessian_h μ p.1 p.1
          + (μ • p.1 + μ • 𝓢.f_lhscb.grad p.1 + p.2.2.1 • p.1)
          - p.2.2.2 • 𝓢.e_τ) basepoint := by
    have h_first : ContDiffAt ℝ 1
        (fun p : H X Y × (H X Y × ℝ × ℝ) =>
          (𝓢.hessian_h μ p.1 + 𝓢.M_clm) (p.1 + p.2.1)) basepoint := by
      show ContDiffAt ℝ 1
        (fun p : H X Y × (H X Y × ℝ × ℝ) =>
          𝓢.hessian_h μ p.1 (p.1 + p.2.1) + 𝓢.M_clm (p.1 + p.2.1)) basepoint
      exact h_H_uk_v.add h_M_clm
    have h_const_μ_uk : ContDiffAt ℝ 1
        (fun p : H X Y × (H X Y × ℝ × ℝ) => μ • p.1) basepoint :=
      h_uk.const_smul μ
    have h_const_μ_grad : ContDiffAt ℝ 1
        (fun p : H X Y × (H X Y × ℝ × ℝ) =>
          μ • 𝓢.f_lhscb.grad p.1) basepoint :=
      h_grad_pcomp.const_smul μ
    have h_lam_uk : ContDiffAt ℝ 1
        (fun p : H X Y × (H X Y × ℝ × ℝ) => p.2.2.1 • p.1) basepoint :=
      h_lam.smul h_uk
    have h_th_eτ : ContDiffAt ℝ 1
        (fun p : H X Y × (H X Y × ℝ × ℝ) => p.2.2.2 • 𝓢.e_τ) basepoint :=
      h_th.smul contDiffAt_const
    exact ((h_first.sub h_H_uk_uk).add
            ((h_const_μ_uk.add h_const_μ_grad).add h_lam_uk)).sub h_th_eτ
  -- Tangency residual is C^∞ (bilinear inner).
  have h_tangency : ContDiffAt ℝ 1
      (fun p : H X Y × (H X Y × ℝ × ℝ) => inner ℝ p.1 p.2.1) basepoint := by
    have h_inner_cd : ContDiff ℝ ⊤
        (fun q : H X Y × H X Y => inner ℝ q.1 q.2 : H X Y × H X Y → ℝ) :=
      (isBoundedBilinearMap_inner (𝕜 := ℝ) (E := H X Y)).contDiff
    have h_pair : ContDiffAt ℝ 1
        (fun p : H X Y × (H X Y × ℝ × ℝ) => (p.1, p.2.1)) basepoint :=
      h_uk.prodMk h_v
    exact (h_inner_cd.contDiffAt.of_le le_top).fun_comp _ h_pair
  -- Scalar residual is C^∞.
  have h_scalar : ContDiffAt ℝ 1
      (fun p : H X Y × (H X Y × ℝ × ℝ) =>
        p.2.2.2 * 𝓢.tau_proj (p.1 + p.2.1)
          - 𝓢.Px_bilinform_clm (p.1 + p.2.1) (p.1 + p.2.1) - μ) basepoint := by
    have h_tau : ContDiffAt ℝ 1
        (fun p : H X Y × (H X Y × ℝ × ℝ) =>
          𝓢.tau_proj (p.1 + p.2.1)) basepoint :=
      ((IrnSetup.tau_proj_linear : H X Y →L[ℝ] ℝ).contDiff.contDiffAt).fun_comp _ h_uk_v
    have h_th_tau : ContDiffAt ℝ 1
        (fun p : H X Y × (H X Y × ℝ × ℝ) =>
          p.2.2.2 * 𝓢.tau_proj (p.1 + p.2.1)) basepoint :=
      h_th.mul h_tau
    have h_Px : ContDiffAt ℝ 1
        (fun p : H X Y × (H X Y × ℝ × ℝ) =>
          𝓢.Px_bilinform_clm (p.1 + p.2.1) (p.1 + p.2.1)) basepoint := by
      have h_bilin_cd : ContDiff ℝ ⊤
          (fun q : H X Y × H X Y => 𝓢.Px_bilinform_clm q.1 q.2) := by
        exact (𝓢.Px_bilinform_clm.isBoundedBilinearMap).contDiff
      have h_pair : ContDiffAt ℝ 1
          (fun p : H X Y × (H X Y × ℝ × ℝ) =>
            (p.1 + p.2.1, p.1 + p.2.1)) basepoint :=
        h_uk_v.prodMk h_uk_v
      exact (h_bilin_cd.contDiffAt.of_le le_top).fun_comp _ h_pair
    exact (h_th_tau.sub h_Px).sub contDiffAt_const
  -- Combine all three components into the product.
  show ContDiffAt ℝ 1 (𝓢.rjnSystem μ) basepoint
  show ContDiffAt ℝ 1 (fun p : H X Y × (H X Y × ℝ × ℝ) =>
    ((𝓢.hessian_h μ p.1 + 𝓢.M_clm) (p.1 + p.2.1)
        - 𝓢.hessian_h μ p.1 p.1
        + (μ • p.1 + μ • 𝓢.f_lhscb.grad p.1 + p.2.2.1 • p.1)
        - p.2.2.2 • 𝓢.e_τ,
      inner ℝ p.1 p.2.1,
      p.2.2.2 * 𝓢.tau_proj (p.1 + p.2.1)
        - 𝓢.Px_bilinform_clm (p.1 + p.2.1) (p.1 + p.2.1) - μ)) basepoint
  exact h_newton.prodMk (h_tangency.prodMk h_scalar)

/-- **Uniqueness of the RJN tangent solution at `u*(μ)`.** At
`u_k = u*(μ)` the Riemannian semi-Newton tangent inclusion admits
`v = 0` as a solution (`IsRjnSolution.zero_at_centralPath`); this
lemma states `v = 0` is the *unique* such solution.

Now a direct corollary of the global-uniqueness lemma
`IsRjnSolution.unique` (paper §5.5 Proposition 11(a)): given any
two `IsRjnSolution` witnesses at `u_k = u*(μ)`, they are equal;
applied to the candidate `v` and the witness `0` it yields `v = 0`.
Sphere membership of `u*(μ)` follows from `centralPath_norm_sq`
(paper Proposition 4). -/
theorem IsRjnSolution.at_centralPath_unique {μ : ℝ} (hμ : 0 < μ)
    {v : H X Y}
    (hv : 𝓢.IsRjnSolution μ (𝓢.centralPathPoint μ hμ) v) : v = 0 := by
  set u_star := 𝓢.centralPathPoint μ hμ with hu_star_def
  have h_cpp : 𝓢.IsCentralPathPoint μ u_star :=
    𝓢.centralPathPoint_isCentralPathPoint μ hμ
  have hu_star_C : u_star ∈ 𝓢.C_interior := h_cpp.1
  have hu_star_S : u_star ∈ 𝓢.sphere := by
    show ‖u_star‖ = 𝓢.r
    have h_norm_sq : ‖u_star‖ ^ 2 = (𝓢.ν : ℝ) + 1 :=
      𝓢.centralPath_norm_sq hμ h_cpp
    have h_r_sq : 𝓢.r ^ 2 = (𝓢.ν : ℝ) + 1 := 𝓢.r_sq
    have h_eq_sq : ‖u_star‖ ^ 2 = 𝓢.r ^ 2 := by rw [h_norm_sq, ← h_r_sq]
    have h_sqrt : Real.sqrt (‖u_star‖ ^ 2) = Real.sqrt (𝓢.r ^ 2) := by
      rw [h_eq_sq]
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq 𝓢.r_pos.le] at h_sqrt
  have h_zero : 𝓢.IsRjnSolution μ u_star 0 :=
    IsRjnSolution.zero_at_centralPath 𝓢 hμ
  exact IsRjnSolution.unique 𝓢 hμ hu_star_S hu_star_C hv h_zero

/-- **The Newton direction vanishes at `u*(μ)`.** The base case of
the basin theorem: at the centre of the basin, `rjnDirection μ u* = 0`,
so both bounds in `rjnDirection_linear_bound` and
`rjnDirection_tangent_step_quadratic_bound` reduce to `0 ≤ 0`.
Combines `rjnDirection_isRjnSolution_at_centralPath` (the chosen
direction is a Variant C solution) with
`IsRjnSolution.at_centralPath_unique` (the only such solution is `0`). -/
theorem rjnDirection_at_centralPath_eq_zero {μ : ℝ} (hμ : 0 < μ) :
    𝓢.rjnDirection μ (𝓢.centralPathPoint μ hμ) = 0 :=
  IsRjnSolution.at_centralPath_unique 𝓢 hμ
    (𝓢.rjnDirection_isRjnSolution_at_centralPath hμ)

/-- **Local Lipschitz continuity of `rjnDirection`** (sorry — paper
Proposition 11(b), IFT half). In a Euclidean ball around `u*(μ)`,
`rjnDirection μ` is Lipschitz with some constant `C`.

**Sorry.** Paper proof (Proposition 11(b)): the RJN tangent
inclusion in the bundle `(v, λ, θ)` is a `C¹` system in `u` whose
partial derivative in `(v, λ, θ)` at `(u*, 0, 0, θ*)` is invertible.
The implicit function theorem produces a `C¹` map `u ↦ (v(u), λ(u), θ(u))`
with `(v(u*), λ(u*), θ(u*)) = (0, 0, θ*)`; combined with the
*global* uniqueness lemma `IsRjnSolution.unique`, the IFT branch
`v(u)` agrees with `rjnDirection μ u` on the IFT neighbourhood
without any further IFT-branch side-condition. Lipschitz continuity
follows from the bounded derivative of `v` on a compact ball. -/
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
proof chain are `IsRjnSolution.unique` (paper Proposition 11(a)),
`rjnDirection_locallyLipschitz` (paper Proposition 11(b)), and
`rjnDirection_tangent_step_quadratic_bound` (paper Theorem 12,
Newton-identity half); the retraction half is fully formalized in
`Sphere.expMap_sub_add_norm_le`. -/
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
