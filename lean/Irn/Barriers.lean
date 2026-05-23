/-
# Barriers (paper §2.1)

Logarithmically homogeneous self-concordant barriers (LHSCB) and the
conjugate barrier-gradient maps `F*`, `G*`, `φ`.

An `LHSCB V K ν` is a `ν`-LHSCB on the (convex) cone `K ⊆ V`. The
barrier function `f` is `C³` on `int(K)` and satisfies the standard
third-derivative self-concordance bound. The gradient `∇f` is a
*derived* definition: `grad x := (toDual ℝ V).symm (fderiv ℝ f x)`,
i.e. the Riesz representation of the Fréchet derivative.

Required fields:

* `contDiff` — `f` is `C³` on `int(K)`;
* `self_concordant` — squared SC bound
  `(D³f(x)[h,h,h])² ≤ 4 · (D²f(x)[h,h])³`, which implies `D²f ≥ 0`
  (so this packages convexity);
* `log_homog` — `f(t x) = f(x) - ν log t` for `x ∈ int(K)` and `t > 0`;
* `barrier` — `f(x) → +∞` at `frontier K`.

Derived:

* `grad` — `(toDual ℝ V).symm (fderiv ℝ f x)`;
* `euler` — `⟨u, ∇f(u)⟩ = -ν`, proven from `log_homog` by differentiating
  `f(t · u) = f(u) - ν · log t` at `t = 1`;
* `grad_monotone` — convexity in gradient form, proven from
  `self_concordant_hessian_nonneg` via monotonicity of the Hessian
  quadratic form along the segment `v + t(u - v)`;
* `grad_inequality` — first-order convexity inequality
  `f(v) ≥ f(u) + ⟨∇f(u), v - u⟩`;
* `grad_norm_tendsto_atTop` — `‖∇f(u)‖ → ∞` at the boundary of `K`.

Other API:

* `LHSCB.add` — sum of a `ν₁`-LHSCB on `K₁` and a `ν₂`-LHSCB on `K₂`
  is a `(ν₁+ν₂)`-LHSCB on `K₁ ∩ K₂`. Uses `interior_inter`.
* `LHSCB.add_grad` — derived gradient of the sum equals the sum of
  derived gradients (via `fderiv.add` + Riesz linearity).
* `LHSCB.hessian_fderiv_apply_self` — `(∇²f x) x = -∇f x` (and its
  inner-product variant).
* `LHSCB.IsStrict` — separate predicate for strict convexity on
  `int(K)` (lifted barriers do not satisfy this).

Paper references:
* §2.1 Definition 2 (`ν`-LHSCB)
* §2.1 eq. `eq:euler-id` (Euler identity)
* §2.1 (conjugate barriers `f*`, `g*`, `φ`)
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace Irn

open scoped InnerProductSpace

/-- An abstract `ν`-LHSCB of smoothness degree `d ≥ 3` on a real inner
product space `V` with respect to the (convex) cone `K ⊆ V`.

`d : ℕ∞` is the `ContDiffOn`-degree of `f` on `int(K)` (with `d = ⊤`
allowing `C^∞` barriers). The minimum `d = 3` is the smoothness needed
for the self-concordance bound (which references the third derivative).

The gradient is *not* a field — see `LHSCB.grad`. -/
structure LHSCB (V : Type*)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (K : Set V) (ν : ℕ) (d : ℕ∞) where
  /-- The smoothness degree `d` is at least `3` (required so that the
  self-concordance bound, which uses third-order derivatives, is well
  defined). -/
  hd_ge : (3 : ℕ∞) ≤ d
  /-- The domain `K` is convex. Together with the LHSCB structure this
  expresses that `f` is a barrier for a convex (cone) domain — the
  setting in which the Nesterov–Nemirovski machinery applies. The
  `interior K` is then also convex (`Convex.interior`), so the segment
  `[u₀, u]` between any two interior points lies in `interior K`. -/
  convex_K : Convex ℝ K
  /-- The barrier function. -/
  f : V → ℝ
  /-- `f` is `C^d` on `int(K)`. -/
  contDiff : ContDiffOn ℝ d f (interior K)
  /-- **Self-concordance bound** (squared form). On `int(K)`:
  `(D³f(x)[h,h,h])² ≤ 4 · (D²f(x)[h,h])³`. This implies `D²f ≥ 0`
  (since the LHS is nonneg but the RHS is the cube of `D²f[h,h]`),
  so convexity is packaged here. -/
  self_concordant : ∀ x ∈ interior K, ∀ h : V,
    (iteratedFDerivWithin ℝ 3 f (interior K) x (fun _ => h)) ^ 2 ≤
      4 * (iteratedFDerivWithin ℝ 2 f (interior K) x (fun _ => h)) ^ 3
  /-- **Logarithmic homogeneity of degree `-ν`**:
  `f(t · x) = f(x) - ν · log t` for `x ∈ int(K)` and `t > 0`. -/
  log_homog : ∀ x ∈ interior K, ∀ t : ℝ, 0 < t →
    f (t • x) = f x - (ν : ℝ) * Real.log t
  /-- **Barrier property**: `f(x) → +∞` as `x` approaches `∂K` from
  inside. -/
  barrier : ∀ x ∈ frontier K,
    Filter.Tendsto f (nhdsWithin x (interior K)) Filter.atTop

namespace LHSCB

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V]

/-- The **gradient** `∇f(x)` of an LHSCB, as the Riesz representation
of `fderiv ℝ f x`. Outside `int(K)` the value is whatever Mathlib's
`fderiv` returns when `f` is not differentiable (typically `0`). -/
noncomputable def grad {K : Set V} {ν : ℕ} {d : ℕ∞} (f : LHSCB V K ν d) :
    V → V :=
  fun x => (InnerProductSpace.toDual ℝ V).symm (fderiv ℝ f.f x)

omit [CompleteSpace V] in
/-- `f` is `C^3` on `int(K)`: downgrade `f.contDiff` (which gives
`C^d`) using `f.hd_ge : 3 ≤ d`. -/
theorem contDiff₃ {K : Set V} {ν : ℕ} {d : ℕ∞} (f : LHSCB V K ν d) :
    ContDiffOn ℝ 3 f.f (interior K) := by
  have h : ((3 : ℕ∞) : WithTop ℕ∞) ≤ (d : WithTop ℕ∞) := by
    exact_mod_cast f.hd_ge
  exact f.contDiff.of_le h

/-- **Algebraic core of the self-concordance sum.** If `a² ≤ 4p³`,
`b² ≤ 4q³`, `p ≥ 0`, `q ≥ 0`, then `(a + b)² ≤ 4(p + q)³`. The case
split on `p = 0` / `q = 0` handles degenerate cases; the generic
case uses `nlinarith` with `sq_nonneg (a*q - b*p)` as the key hint
(this expands to `2 a b p q ≤ a² q² + b² p² ≤ 4 p³ q² + 4 p² q³`,
which combined with the cube bounds gives the inequality). -/
lemma sc_sum_ineq {a b p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (ha : a ^ 2 ≤ 4 * p ^ 3) (hb : b ^ 2 ≤ 4 * q ^ 3) :
    (a + b) ^ 2 ≤ 4 * (p + q) ^ 3 := by
  by_cases hp0 : p = 0 <;> by_cases hq0 : q = 0 <;> simp_all +decide [pow_succ]
  · norm_num [show a = 0 by nlinarith, show b = 0 by nlinarith]
  · norm_num [show a = 0 by nlinarith] at *; nlinarith
  · norm_num [show b = 0 by nlinarith] at *; nlinarith
  · nlinarith [sq_nonneg (a * q - b * p),
      show 0 < p * q by positivity,
      show 0 < p ^ 2 * q by positivity,
      show 0 < p * q ^ 2 by positivity,
      show 0 < p ^ 3 by positivity,
      show 0 < q ^ 3 by positivity]

/-- **Self-concordance is preserved under right composition with a
continuous linear map.** If `f` is `C³` on the open set `s ⊆ W` and
satisfies the squared SC bound there, then for any CLM `L : V → W`,
the function `f ∘ L` is `C³` on `L⁻¹ s` and satisfies the SC bound
there too. Uses `ContinuousLinearMap.iteratedFDerivWithin_comp_right`. -/
lemma self_concordant_comp_right_clm
    {V' W' : Type*}
    [NormedAddCommGroup V'] [NormedSpace ℝ V']
    [NormedAddCommGroup W'] [NormedSpace ℝ W']
    {s : Set W'} (hs : IsOpen s)
    {f : W' → ℝ} (hf_diff : ContDiffOn ℝ 3 f s)
    (hf_sc : ∀ x ∈ s, ∀ h : W',
      (iteratedFDerivWithin ℝ 3 f s x (fun _ => h)) ^ 2 ≤
        4 * (iteratedFDerivWithin ℝ 2 f s x (fun _ => h)) ^ 3)
    (L : V' →L[ℝ] W') :
    ∀ x ∈ L ⁻¹' s, ∀ h : V',
      (iteratedFDerivWithin ℝ 3 (f ∘ L) (L ⁻¹' s) x (fun _ => h)) ^ 2 ≤
        4 * (iteratedFDerivWithin ℝ 2 (f ∘ L) (L ⁻¹' s) x (fun _ => h)) ^ 3 := by
  intro x hx h
  have hs_diff : UniqueDiffOn ℝ s := hs.uniqueDiffOn
  have hs'_diff : UniqueDiffOn ℝ (L ⁻¹' s) := (hs.preimage L.continuous).uniqueDiffOn
  have hLxs : L x ∈ s := hx
  have h2_eq : iteratedFDerivWithin ℝ 2 (f ∘ L) (L ⁻¹' s) x (fun _ => h)
             = iteratedFDerivWithin ℝ 2 f s (L x) (fun _ => L h) := by
    rw [L.iteratedFDerivWithin_comp_right hf_diff hs_diff hs'_diff hLxs (by norm_num)]
    rfl
  have h3_eq : iteratedFDerivWithin ℝ 3 (f ∘ L) (L ⁻¹' s) x (fun _ => h)
             = iteratedFDerivWithin ℝ 3 f s (L x) (fun _ => L h) := by
    rw [L.iteratedFDerivWithin_comp_right hf_diff hs_diff hs'_diff hLxs (by norm_num)]
    rfl
  rw [h2_eq, h3_eq]
  exact hf_sc (L x) hLxs (L h)

omit [CompleteSpace V] in
/-- **Hessian non-negativity from SC bound.** The squared SC bound
forces `D²f(x)[h,h] ≥ 0` (the cube of a negative is negative, but
the LHS is a square). -/
lemma self_concordant_hessian_nonneg {K : Set V} {ν : ℕ} {d : ℕ∞}
    (f : LHSCB V K ν d) :
    ∀ x ∈ interior K, ∀ h : V,
      0 ≤ iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => h) := by
  intro x hx h
  by_contra hneg
  replace hneg : iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => h) < 0 :=
    not_le.mp hneg
  have hsc := f.self_concordant x hx h
  have h_cube : (iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => h)) ^ 3 < 0 :=
    Odd.pow_neg (by decide : Odd 3) hneg
  have h_sq : 0 ≤ (iteratedFDerivWithin ℝ 3 f.f (interior K) x (fun _ => h)) ^ 2 :=
    sq_nonneg _
  linarith

/-! ### Dikin-ball Hessian Lipschitz bound (Nesterov–Nemirovski)

The squared self-concordance bound `(D³f)² ≤ 4(D²f)³` integrates to a
multiplicative bound on the Hessian inside the **Dikin ball** of any
point. Specifically, for `r = ‖u − u₀‖_{∇²f(u₀)} < 1` and any direction
`h ∈ V`:
`(1 − r)² ⟨h, ∇²f(u₀) h⟩ ≤ ⟨h, ∇²f(u) h⟩ ≤ (1 − r)⁻² ⟨h, ∇²f(u₀) h⟩`.

This is **paper §6.3 Lemma 16 step (i)** ("self-concordance of `W`"):
the Lipschitz constant of `∇²f` in the local SC norm is an absolute
constant. It is the analytic input that lets the Newton–Kantorovich
analysis give a basin radius `ρ*` independent of `μ` — without it the
basin would shrink near `∂K`.

**Standard proof (Nesterov–Nemirovski §2.1):**
1. **Polarized SC bound.** From `(D³f(x)[h, h, h])² ≤ 4 (D²f(x)[h, h])³`
   derive, via polarization of the symmetric trilinear form,
   `|D³f(x)[a, b, c]| ≤ 2 ‖a‖_{∇²f(x)} ‖b‖_{∇²f(x)} ‖c‖_{∇²f(x)}`.
2. **Diagonal ODE.** Restrict to the line `t ↦ u₀ + t · d` (where
   `d = u − u₀`). Let `a(t) := ⟨d, ∇²f(u₀ + t·d) d⟩`. Then
   `a'(t) = D³f(...)[d, d, d]`, and the squared SC bound at direction
   `d` gives `|a'(t)| ≤ 2 a(t)^(3/2)`. So `φ(t) := a(t)^(−1/2)`
   satisfies `|φ'(t)| ≤ 1`; integrating gives the diagonal bound
   `a(s) ≤ a(0) / (1 − s · √a(0))²` for `s · √a(0) < 1`.
3. **Polarized lift.** For arbitrary `h`, let `ψ(t) := ⟨h, ∇²f(u₀ +
   t·d) h⟩`. By polarized SC,
   `|ψ'(t)| = |D³f[d, h, h]| ≤ 2 ‖d‖_{∇²f(u₀+t·d)} · ψ(t)`. Bound
   `‖d‖_{∇²f(u₀+t·d)} ≤ r/(1 − tr)` by Step 2 (with the displacement
   `d` itself), giving `|d/dt log ψ(t)| ≤ 2r/(1−tr)`. Integrate from
   `0` to `1`: `∫₀¹ 2r/(1−sr) ds = −2 log(1−r)`, so `ψ(1)/ψ(0) ∈
   [(1−r)², (1−r)⁻²]`. -/

omit [CompleteSpace V] in
/-- **Univariate SC core (step 2's seed).** Squared SC at a fixed
direction `h` says `(D³f[h,h,h])² ≤ 4 (D²f[h,h])³`. Equivalently, for
`a := D²f[h,h]` and `b := D³f[h,h,h]`, `|b| ≤ 2 a^(3/2)` (after
extracting square root, since `a ≥ 0`). This is the form that feeds
the diagonal ODE `|d/dt (a(t))^(−1/2)| ≤ 1`. -/
lemma self_concordant_abs_third {K : Set V} {ν : ℕ} {d : ℕ∞}
    (f : LHSCB V K ν d) (x : V) (hx : x ∈ interior K) (h : V) :
    |iteratedFDerivWithin ℝ 3 f.f (interior K) x (fun _ => h)| ≤
      2 * Real.sqrt
        (iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => h)) ^ 3 := by
  set a : ℝ := iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => h) with ha_def
  set b : ℝ := iteratedFDerivWithin ℝ 3 f.f (interior K) x (fun _ => h) with hb_def
  have ha_nn : 0 ≤ a := f.self_concordant_hessian_nonneg x hx h
  have hsc : b ^ 2 ≤ 4 * a ^ 3 := f.self_concordant x hx h
  -- |b|² = b² ≤ 4·a³ = (2·√a³)² = (2·(√a)³)².
  have h_sqrt_a_nn : 0 ≤ Real.sqrt a := Real.sqrt_nonneg _
  have h_sqrt_a_cubed_nn : 0 ≤ Real.sqrt a ^ 3 := by positivity
  have h_rhs_nn : 0 ≤ 2 * Real.sqrt a ^ 3 := by positivity
  have h_rhs_sq : (2 * Real.sqrt a ^ 3) ^ 2 = 4 * a ^ 3 := by
    rw [mul_pow, show ((Real.sqrt a) ^ 3) ^ 2 = ((Real.sqrt a) ^ 2) ^ 3 from by ring,
        Real.sq_sqrt ha_nn]; norm_num
  have h_abs_sq_le : |b| ^ 2 ≤ (2 * Real.sqrt a ^ 3) ^ 2 := by
    rw [sq_abs, h_rhs_sq]; exact hsc
  exact (abs_le_of_sq_le_sq' h_abs_sq_le h_rhs_nn).2

/-! ### Dikin-ball Hessian Lipschitz bound — scaffold

The bound is decomposed into four auxiliary lemmas plus a top-level
theorem, following the standard Nesterov–Nemirovski outline:

1. `segment_in_interior` — the line segment `[u₀, u]` stays in
   `interior K` (convex preimage of `interior K`, which is itself
   convex by `Convex.interior` on `f.convex_K`).
2. `dikin_path_metric_bound` — the seed `a(t) ≤ a(0)/(1 − tr)²`
   estimate from the diagonal SC ODE.
3. `path_hess_deriv_bound` — the polarized derivative bound for
   `t ↦ hess f (u₀ + t·(u−u₀)) h`.
4. `path_hess_integrated_bound` — integrate (3) against (2) to get
   `(1−r)² · hess f u₀ h ≤ hess f u h ≤ (1−r)⁻² · hess f u₀ h`.

The final `hessian_dikin_bound` is then just a thin wrapper that
unfolds `hess` back to the `iteratedFDerivWithin`-spelling used
downstream. All five carry `sorry` for now. -/

end LHSCB

/-- Convenience abbreviation for the Hessian quadratic form
`D²f(x)[h, h]` taken inside `interior K`. -/
noncomputable def hess {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : V → ℝ) (K : Set V) (x h : V) : ℝ :=
  iteratedFDerivWithin ℝ 2 f (interior K) x (fun _ => h)

/-- The local Hessian-induced (semi)norm along direction `v`:
`‖v‖_{∇²f(x)} = √(D²f(x)[v,v])`. -/
noncomputable def local_norm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : V → ℝ) (K : Set V) (x v : V) : ℝ :=
  Real.sqrt (hess f K x v)

/-- The interior of a convex set is convex, so the segment between
two interior points lies in the interior. -/
lemma segment_in_interior {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {K : Set V} (hK_convex : Convex ℝ K)
    (u₀ : V) (hu₀ : u₀ ∈ interior K)
    (u : V) (hu : u ∈ interior K) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, u₀ + t • (u - u₀) ∈ interior K := by
  intro t ⟨h0, h1⟩
  have h_eq : u₀ + t • (u - u₀) = (1 - t) • u₀ + t • u := by
    rw [smul_sub, sub_smul, one_smul]; abel
  rw [h_eq]
  exact hK_convex.interior hu₀ hu (by linarith) h0 (by linarith)

/-! ### Path-derivative scaffold (pure real analysis)

Two real-analysis Gronwall/ODE-integration lemmas, isolated from the
LHSCB context. Both are strictly simpler than `dikin_path_metric_bound`
and `path_hess_integrated_bound` because they have no self-concordance
content — they take the ODE inequality as a hypothesis on an abstract
function `a : ℝ → ℝ` (resp. `H : ℝ → ℝ`) and integrate it. -/

/-- **ε-regularized substitution is 1-Lipschitz.** For any `ε > 0`, the
function `b_ε(s) := 1/√(a(s) + ε²)` is 1-Lipschitz on `[0, 1]`,
provided `a` is non-negative, continuous, and differentiable on `(0,1)`
with `|a'(t)| ≤ 2 (√a(t))³`.

Pure real-analysis fact, no LHSCB context. Expected proof: differentiate
`b_ε` (composition of `a`, `Real.sqrt`, and reciprocal — all smooth on
the positive domain), bound `|b_ε'(s)| ≤ 1` via the ODE hypothesis (the
key cancellation: `|a'|/(2·(a+ε²)^(3/2)) ≤ a^(3/2)/(a+ε²)^(3/2) ≤ 1`),
then apply `lipschitzOnWith_of_nnnorm_deriv_le` on the convex `Ioo 0 1`
and `LipschitzOnWith.closure` to extend to `[0, 1]`. -/
private lemma b_eps_one_lipschitz
    {a : ℝ → ℝ}
    (ha_nn : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ a t)
    (ha_cont : ContinuousOn a (Set.Icc (0:ℝ) 1))
    (ha_deriv : ∀ t ∈ Set.Ioo (0:ℝ) 1, ∃ a', HasDerivAt a a' t ∧
                |a'| ≤ 2 * (Real.sqrt (a t)) ^ 3)
    (ε : ℝ) (hε_pos : 0 < ε) :
    LipschitzOnWith 1 (fun s => 1 / Real.sqrt (a s + ε ^ 2))
      (Set.Icc (0:ℝ) 1) := by
  set b : ℝ → ℝ := fun s => 1 / Real.sqrt (a s + ε ^ 2) with hb_def
  have hε_sq_pos : (0 : ℝ) < ε ^ 2 := pow_pos hε_pos 2
  have h_pos : ∀ s ∈ Set.Icc (0:ℝ) 1, (0:ℝ) < a s + ε ^ 2 := fun s hs => by
    have := ha_nn s hs; linarith
  have h_sqrt_pos : ∀ s ∈ Set.Icc (0:ℝ) 1, (0:ℝ) < Real.sqrt (a s + ε ^ 2) :=
    fun s hs => Real.sqrt_pos.mpr (h_pos s hs)
  -- Continuity of `b` on `[0, 1]`.
  have hb_cont : ContinuousOn b (Set.Icc (0:ℝ) 1) := by
    refine continuousOn_const.div ?_ (fun s hs => ne_of_gt (h_sqrt_pos s hs))
    exact Real.continuous_sqrt.comp_continuousOn (ha_cont.add continuousOn_const)
  -- Differentiability + derivative bound on `(0, 1)`.
  have hb_diff_deriv :
      ∀ x ∈ Set.Ioo (0:ℝ) 1, DifferentiableAt ℝ b x ∧ ‖deriv b x‖ ≤ 1 := by
    intro x hx
    have hx_Icc : x ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    obtain ⟨a', hda', hbd⟩ := ha_deriv x hx
    have h_pos_x := h_pos x hx_Icc
    have h_sqrt_pos_x := h_sqrt_pos x hx_Icc
    have h_sqrt_ne_x : Real.sqrt (a x + ε ^ 2) ≠ 0 := ne_of_gt h_sqrt_pos_x
    have h_pos_ne : (a x + ε ^ 2) ≠ 0 := ne_of_gt h_pos_x
    -- Chain rule: b'(x) = -(a' / (2·√(a+ε²))) / (√(a+ε²))².
    have h_add : HasDerivAt (fun s => a s + ε ^ 2) a' x := hda'.add_const _
    have h_sqrt : HasDerivAt (fun s => Real.sqrt (a s + ε ^ 2))
        (a' / (2 * Real.sqrt (a x + ε ^ 2))) x := by
      have h_root :
          HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (a x + ε ^ 2))) (a x + ε ^ 2) :=
        Real.hasDerivAt_sqrt h_pos_ne
      have h_comp := h_root.comp x h_add
      convert h_comp using 1
      field_simp
    have h_inv : HasDerivAt b
        ((0 * Real.sqrt (a x + ε ^ 2) -
            1 * (a' / (2 * Real.sqrt (a x + ε ^ 2))))
          / Real.sqrt (a x + ε ^ 2) ^ 2) x :=
      (hasDerivAt_const x (1:ℝ)).div h_sqrt h_sqrt_ne_x
    refine ⟨h_inv.differentiableAt, ?_⟩
    rw [h_inv.deriv]
    -- Bound |b'(x)| = |a'| / (2 · (√(a+ε²))³) ≤ 1.
    have h_a_nn_x : 0 ≤ a x := ha_nn x hx_Icc
    have h_sqrt_a_nn : 0 ≤ Real.sqrt (a x) := Real.sqrt_nonneg _
    have h_sqrt_a_le : Real.sqrt (a x) ≤ Real.sqrt (a x + ε ^ 2) :=
      Real.sqrt_le_sqrt (by linarith)
    have h_sqrt_a_cubed_le :
        (Real.sqrt (a x)) ^ 3 ≤ (Real.sqrt (a x + ε ^ 2)) ^ 3 :=
      pow_le_pow_left₀ h_sqrt_a_nn h_sqrt_a_le 3
    have h_abs_a'_bd : |a'| ≤ 2 * (Real.sqrt (a x + ε ^ 2)) ^ 3 := by
      calc |a'|
          ≤ 2 * (Real.sqrt (a x)) ^ 3 := hbd
        _ ≤ 2 * (Real.sqrt (a x + ε ^ 2)) ^ 3 := by linarith
    have h_sqrt_cubed_pos : (0 : ℝ) < (Real.sqrt (a x + ε ^ 2)) ^ 3 :=
      pow_pos h_sqrt_pos_x 3
    have h_sqrt_sq_pos : (0 : ℝ) < (Real.sqrt (a x + ε ^ 2)) ^ 2 :=
      pow_pos h_sqrt_pos_x 2
    have h_two_sqrt_pos : (0 : ℝ) < 2 * Real.sqrt (a x + ε ^ 2) := by positivity
    -- Simplify the deriv expression and bound it.
    have h_eq_deriv :
        (0 * Real.sqrt (a x + ε ^ 2) - 1 * (a' / (2 * Real.sqrt (a x + ε ^ 2))))
            / Real.sqrt (a x + ε ^ 2) ^ 2
          = -a' / (2 * (Real.sqrt (a x + ε ^ 2)) ^ 3) := by
      field_simp
      ring
    rw [h_eq_deriv]
    rw [Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos (by positivity :
        (0 : ℝ) < 2 * (Real.sqrt (a x + ε ^ 2)) ^ 3)]
    rw [div_le_one (by positivity : (0 : ℝ) < 2 * (Real.sqrt (a x + ε ^ 2)) ^ 3)]
    exact h_abs_a'_bd
  -- 1-Lipschitz on `Ioo 0 1`.
  have hb_lip_Ioo : LipschitzOnWith 1 b (Set.Ioo (0:ℝ) 1) :=
    (convex_Ioo (0:ℝ) 1).lipschitzOnWith_of_nnnorm_deriv_le
      (fun x hx => (hb_diff_deriv x hx).1)
      (fun x hx => by
        have h := (hb_diff_deriv x hx).2; exact_mod_cast h)
  -- Extend to `Icc 0 1` via continuity.
  have h_closure : closure (Set.Ioo (0:ℝ) 1) = Set.Icc (0:ℝ) 1 :=
    closure_Ioo (by norm_num)
  have hb_cont' : ContinuousOn b (closure (Set.Ioo (0:ℝ) 1)) := h_closure ▸ hb_cont
  have h := hb_lip_Ioo.closure hb_cont'
  rwa [h_closure] at h

/-- **Squared diagonal bound from Lipschitz family.** Given the 1-Lipschitz
family `b_ε := 1/√(a+ε²)` on `[0, 1]` (one per `ε > 0`), conclude the
squared Dikin bound `(1 − t·r)² · a(t) ≤ r²`.

Pure real-analysis limit argument, no derivative computations: from
1-Lipschitz `|b_ε(t) − b_ε(0)| ≤ t` and `a(0) ≤ r²` (so `b_ε(0) ≥
1/√(r²+ε²)`), get `√(a(t)+ε²) ≤ 1/(1/√(r²+ε²) − t)` for ε small;
then take `ε → 0+` via `le_of_tendsto` to obtain the squared bound. -/
private lemma diagonal_ode_squared_bound_via_lipschitz
    {a : ℝ → ℝ} {r : ℝ}
    (hr_nn : 0 ≤ r) (hr_lt_one : r < 1)
    (ha_nn : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ a t)
    (ha_0 : a 0 ≤ r ^ 2)
    (h_lip : ∀ ε > (0:ℝ),
        LipschitzOnWith 1 (fun s => 1 / Real.sqrt (a s + ε ^ 2))
          (Set.Icc (0:ℝ) 1)) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, (1 - t * r) ^ 2 * a t ≤ r ^ 2 := by
  intro t ht
  obtain ⟨ht_nn, ht_le⟩ := ht
  rcases eq_or_lt_of_le ht_nn with rfl | ht_pos
  · simpa using ha_0
  -- Main case: `t > 0`.
  -- Family of bounds parameterised by `ε ∈ (0, ε_max)`, where
  -- `ε_max := √(1/t² − r²) > 0`.  Take `ε → 0+` via `le_of_tendsto_of_tendsto'`.
  set g : ℝ → ℝ := fun ε =>
    (1 - t * r) ^ 2 * (r ^ 2 + ε ^ 2) / (1 - t * Real.sqrt (r ^ 2 + ε ^ 2)) ^ 2
    with hg_def
  have h_1tr_pos : (0 : ℝ) < 1 - t * r := by nlinarith
  -- `g 0 = r²`.
  have hg_at_0 : g 0 = r ^ 2 := by
    simp only [g]
    rw [show r ^ 2 + (0:ℝ) ^ 2 = r ^ 2 from by ring, Real.sqrt_sq hr_nn]
    have h_ne : (1 - t * r) ^ 2 ≠ 0 := ne_of_gt (pow_pos h_1tr_pos 2)
    field_simp
  -- `g` continuous at `0` (denominator non-zero).
  have hg_cont : ContinuousAt g 0 := by
    refine ContinuousAt.div ?_ ?_ ?_
    · exact ((continuousAt_const).mul ((continuousAt_const).add
        ((continuousAt_id).pow 2)))
    · refine ContinuousAt.pow ?_ 2
      refine (continuousAt_const).sub ((continuousAt_const).mul ?_)
      exact (Real.continuous_sqrt.continuousAt).comp
        ((continuousAt_const).add ((continuousAt_id).pow 2))
    · simp only [show r ^ 2 + (0:ℝ) ^ 2 = r ^ 2 from by ring, Real.sqrt_sq hr_nn]
      exact ne_of_gt (pow_pos h_1tr_pos 2)
  -- `g` tends to `r²` as `ε → 0+`.
  have h_tendsto : Filter.Tendsto g (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (r ^ 2)) := by
    have h := hg_cont.tendsto
    rw [hg_at_0] at h
    exact h.mono_left nhdsWithin_le_nhds
  -- Useful: `1/t² − r² > 0`.
  have h_t_sq_pos : (0 : ℝ) < t ^ 2 := pow_pos ht_pos 2
  have h_t_sq_le_one : t ^ 2 ≤ 1 := by nlinarith
  have h_inv_t_sq_ge_one : (1 : ℝ) ≤ 1 / t ^ 2 := by
    rw [one_le_div h_t_sq_pos]; exact h_t_sq_le_one
  have h_M_pos : (0 : ℝ) < 1 / t ^ 2 - r ^ 2 := by
    have : r ^ 2 < 1 := by nlinarith
    linarith
  set ε_max : ℝ := Real.sqrt (1 / t ^ 2 - r ^ 2) with hε_max_def
  have hε_max_pos : (0 : ℝ) < ε_max := Real.sqrt_pos.mpr h_M_pos
  -- For each `ε ∈ (0, ε_max)`, `(1 − t·r)² · a(t) ≤ g ε`.
  have h_bound : ∀ ε ∈ Set.Ioo (0:ℝ) ε_max, (1 - t * r) ^ 2 * a t ≤ g ε := by
    intro ε hε
    obtain ⟨hε_pos, hε_lt_max⟩ := hε
    -- Positivity of various quantities.
    have hε_sq_pos : (0 : ℝ) < ε ^ 2 := pow_pos hε_pos 2
    have hr_eps_sq_pos : (0 : ℝ) < r ^ 2 + ε ^ 2 := by positivity
    have h_sqrt_r_eps_pos : (0 : ℝ) < Real.sqrt (r ^ 2 + ε ^ 2) :=
      Real.sqrt_pos.mpr hr_eps_sq_pos
    -- `ε² < 1/t² − r²` (squaring `ε < ε_max`).
    have hε_sq_lt : ε ^ 2 < 1 / t ^ 2 - r ^ 2 := by
      have h_sq_lt : ε ^ 2 < ε_max ^ 2 := by
        have := mul_self_lt_mul_self (le_of_lt hε_pos) hε_lt_max
        simpa [sq] using this
      have hε_max_sq : ε_max ^ 2 = 1 / t ^ 2 - r ^ 2 := by
        rw [hε_max_def]; exact Real.sq_sqrt (le_of_lt h_M_pos)
      linarith
    -- `t·√(r²+ε²) < 1`.
    have h_t_sqrt_lt_one : t * Real.sqrt (r ^ 2 + ε ^ 2) < 1 := by
      have h_sqrt_lt_inv_t : Real.sqrt (r ^ 2 + ε ^ 2) < 1 / t := by
        have h_inv_t_sq : (1 / t) ^ 2 = 1 / t ^ 2 := by field_simp
        have h_lt_inv_sq : r ^ 2 + ε ^ 2 < (1 / t) ^ 2 := by rw [h_inv_t_sq]; linarith
        have h_inv_t_nn : 0 ≤ 1 / t := le_of_lt (by positivity)
        have : Real.sqrt (r ^ 2 + ε ^ 2) < Real.sqrt ((1 / t) ^ 2) :=
          Real.sqrt_lt_sqrt (le_of_lt hr_eps_sq_pos) h_lt_inv_sq
        rwa [Real.sqrt_sq h_inv_t_nn] at this
      have := mul_lt_mul_of_pos_left h_sqrt_lt_inv_t ht_pos
      rwa [mul_one_div, div_self (ne_of_gt ht_pos)] at this
    have h_one_minus_pos : (0 : ℝ) < 1 - t * Real.sqrt (r ^ 2 + ε ^ 2) := by linarith
    -- `1/√(r²+ε²) > t` (used to deduce reciprocal positive).
    have h_inv_gt_t : t < 1 / Real.sqrt (r ^ 2 + ε ^ 2) := by
      rw [lt_div_iff₀ h_sqrt_r_eps_pos]
      linarith
    -- `b_ε(t) ≥ b_ε(0) - t` via Lipschitz.
    have h_lip_t : dist (1 / Real.sqrt (a t + ε ^ 2)) (1 / Real.sqrt (a 0 + ε ^ 2)) ≤ t := by
      have h := (h_lip ε hε_pos).dist_le_mul
        t (Set.mem_Icc.mpr ⟨le_of_lt ht_pos, ht_le⟩)
        0 (Set.mem_Icc.mpr ⟨le_refl _, zero_le_one⟩)
      simpa [Real.dist_eq, abs_of_pos ht_pos] using h
    have h_b_t_ge_b_0_sub_t :
        1 / Real.sqrt (a t + ε ^ 2) ≥ 1 / Real.sqrt (a 0 + ε ^ 2) - t := by
      have h_abs : |1 / Real.sqrt (a t + ε ^ 2) - 1 / Real.sqrt (a 0 + ε ^ 2)| ≤ t :=
        Real.dist_eq _ _ ▸ h_lip_t
      linarith [abs_le.mp h_abs]
    -- `b_ε(0) ≥ 1/√(r²+ε²)`.
    have h_a_0_nn : 0 ≤ a 0 := ha_nn 0 ⟨le_refl _, zero_le_one⟩
    have h_a_0_eps_pos : (0 : ℝ) < a 0 + ε ^ 2 := by linarith
    have h_sqrt_a_0_pos : (0 : ℝ) < Real.sqrt (a 0 + ε ^ 2) :=
      Real.sqrt_pos.mpr h_a_0_eps_pos
    have h_a_0_le : a 0 + ε ^ 2 ≤ r ^ 2 + ε ^ 2 := by linarith
    have h_sqrt_le : Real.sqrt (a 0 + ε ^ 2) ≤ Real.sqrt (r ^ 2 + ε ^ 2) :=
      Real.sqrt_le_sqrt h_a_0_le
    have h_b_0_ge : 1 / Real.sqrt (a 0 + ε ^ 2) ≥ 1 / Real.sqrt (r ^ 2 + ε ^ 2) :=
      one_div_le_one_div_of_le h_sqrt_a_0_pos h_sqrt_le
    -- Combine: `b_ε(t) ≥ 1/√(r²+ε²) − t > 0`.
    have h_b_t_pos_bd :
        1 / Real.sqrt (a t + ε ^ 2) ≥ 1 / Real.sqrt (r ^ 2 + ε ^ 2) - t := by
      linarith
    have h_pos_diff : (0 : ℝ) < 1 / Real.sqrt (r ^ 2 + ε ^ 2) - t := by linarith
    have h_b_t_pos : (0 : ℝ) < 1 / Real.sqrt (a t + ε ^ 2) := by linarith
    -- `√(a(t)+ε²) ≤ √(r²+ε²)/(1 − t·√(r²+ε²))`.
    have h_sqrt_a_t_le :
        Real.sqrt (a t + ε ^ 2) ≤
          Real.sqrt (r ^ 2 + ε ^ 2) / (1 - t * Real.sqrt (r ^ 2 + ε ^ 2)) := by
      have h_recip : Real.sqrt (a t + ε ^ 2) = 1 / (1 / Real.sqrt (a t + ε ^ 2)) := by
        rw [one_div_one_div]
      rw [h_recip]
      have h_le : 1 / (1 / Real.sqrt (a t + ε ^ 2)) ≤
          1 / (1 / Real.sqrt (r ^ 2 + ε ^ 2) - t) :=
        one_div_le_one_div_of_le h_pos_diff h_b_t_pos_bd
      apply h_le.trans
      have h_simp : 1 / (1 / Real.sqrt (r ^ 2 + ε ^ 2) - t) =
          Real.sqrt (r ^ 2 + ε ^ 2) / (1 - t * Real.sqrt (r ^ 2 + ε ^ 2)) := by
        field_simp
      exact le_of_eq h_simp
    -- Square: `a(t) + ε² ≤ (r²+ε²)/(1 − t·√(r²+ε²))²`.
    have h_a_t_eps_nn : 0 ≤ a t + ε ^ 2 := by
      have := ha_nn t ⟨le_of_lt ht_pos, ht_le⟩; linarith
    have h_sqrt_a_t_nn : 0 ≤ Real.sqrt (a t + ε ^ 2) := Real.sqrt_nonneg _
    have h_div_nn :
        0 ≤ Real.sqrt (r ^ 2 + ε ^ 2) / (1 - t * Real.sqrt (r ^ 2 + ε ^ 2)) := by
      exact div_nonneg (Real.sqrt_nonneg _) (le_of_lt h_one_minus_pos)
    have h_sq_le :
        (Real.sqrt (a t + ε ^ 2)) ^ 2 ≤
          (Real.sqrt (r ^ 2 + ε ^ 2) / (1 - t * Real.sqrt (r ^ 2 + ε ^ 2))) ^ 2 :=
      pow_le_pow_left₀ h_sqrt_a_t_nn h_sqrt_a_t_le 2
    rw [Real.sq_sqrt h_a_t_eps_nn,
        div_pow, Real.sq_sqrt (le_of_lt hr_eps_sq_pos)] at h_sq_le
    -- Conclude: `(1−tr)²·a(t) ≤ (1−tr)²·(a(t)+ε²) ≤ (1−tr)²·(r²+ε²)/(1−t·√(r²+ε²))² = g ε`.
    have h_sq_nn : 0 ≤ (1 - t * r) ^ 2 := sq_nonneg _
    calc (1 - t * r) ^ 2 * a t
        ≤ (1 - t * r) ^ 2 * (a t + ε ^ 2) := by nlinarith
      _ ≤ (1 - t * r) ^ 2 *
            ((r ^ 2 + ε ^ 2) / (1 - t * Real.sqrt (r ^ 2 + ε ^ 2)) ^ 2) :=
          mul_le_mul_of_nonneg_left h_sq_le h_sq_nn
      _ = g ε := by rw [hg_def]; ring
  -- Apply `le_of_tendsto_of_tendsto`.
  refine le_of_tendsto_of_tendsto tendsto_const_nhds h_tendsto ?_
  filter_upwards [Ioo_mem_nhdsGT hε_max_pos] with ε hε
  exact h_bound ε hε

/-- **Squared diagonal ODE bound.** Under the same hypotheses as
`local_norm_path_bound_from_diagonal_ode` plus continuity of `a` on
`[0, 1]`, we have `(1 − t·r)² · a(t) ≤ r²` for all `t ∈ [0, 1]`.

This is the squared form of the Dikin estimate; it avoids the
differentiability obstruction at `a = 0` that the natural `1/√a`
substitution would face. The proof is a trivial composition of
`b_eps_one_lipschitz` (1-Lipschitz family from the ODE) and
`diagonal_ode_squared_bound_via_lipschitz` (ε → 0+ limit). -/
private lemma diagonal_ode_squared_bound
    {a : ℝ → ℝ} {r : ℝ}
    (hr_nn : 0 ≤ r) (hr_lt_one : r < 1)
    (ha_nn : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ a t)
    (ha_cont : ContinuousOn a (Set.Icc (0:ℝ) 1))
    (ha_0 : a 0 ≤ r ^ 2)
    (ha_deriv : ∀ t ∈ Set.Ioo (0:ℝ) 1, ∃ a', HasDerivAt a a' t ∧
                |a'| ≤ 2 * (Real.sqrt (a t)) ^ 3) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, (1 - t * r) ^ 2 * a t ≤ r ^ 2 :=
  diagonal_ode_squared_bound_via_lipschitz hr_nn hr_lt_one ha_nn ha_0
    (fun ε hε => b_eps_one_lipschitz ha_nn ha_cont ha_deriv ε hε)

/-- **ODE integration for the diagonal Dikin estimate.** Suppose
`a : ℝ → ℝ` is non-negative and continuous on `[0, 1]`, satisfies
`a(0) ≤ r²` (with `0 ≤ r < 1`), and `|a'(t)| ≤ 2 · (√a(t))³` on `(0, 1)`.
Then `√a(t) ≤ r/(1 − t·r)` for all `t ∈ [0, 1]`.

Proved by taking square roots of the squared form
(`diagonal_ode_squared_bound`): from `(1 − t·r)² · a(t) ≤ r²`,
`√` is monotone, then `√(x² · y) = |x| · √y = (1 − t·r) · √y` (positive),
and the bound is rearranged by dividing by `(1 − t·r) > 0`. -/
lemma local_norm_path_bound_from_diagonal_ode
    {a : ℝ → ℝ} {r : ℝ}
    (ha_nn : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ a t)
    (ha_cont : ContinuousOn a (Set.Icc (0:ℝ) 1))
    (ha_0 : a 0 ≤ r ^ 2)
    (hr_nn : 0 ≤ r) (hr_lt_one : r < 1)
    (ha_deriv : ∀ t ∈ Set.Ioo (0:ℝ) 1, ∃ a', HasDerivAt a a' t ∧
                |a'| ≤ 2 * (Real.sqrt (a t)) ^ 3) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, Real.sqrt (a t) ≤ r / (1 - t * r) := by
  intro t ht
  have h_1tr_pos : (0 : ℝ) < 1 - t * r := by
    obtain ⟨h0, h1⟩ := ht; nlinarith
  have h_sq := diagonal_ode_squared_bound hr_nn hr_lt_one ha_nn ha_cont ha_0 ha_deriv t ht
  -- `h_sq : (1 - t * r) ^ 2 * a t ≤ r ^ 2`. Take square roots.
  have h_sqrt_le :
      Real.sqrt ((1 - t * r) ^ 2 * a t) ≤ Real.sqrt (r ^ 2) :=
    Real.sqrt_le_sqrt h_sq
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq h_1tr_pos.le,
      Real.sqrt_sq hr_nn] at h_sqrt_le
  -- `h_sqrt_le : (1 - t * r) * Real.sqrt (a t) ≤ r`. Divide by `(1 - t * r) > 0`.
  rw [le_div_iff₀ h_1tr_pos, mul_comm]
  exact h_sqrt_le

/-- **Multiplicative Gronwall along an affine SC path.** Suppose
`H : ℝ → ℝ` is non-negative and continuous on `[0, 1]` and satisfies the
log-derivative bound `|H'(t)| ≤ 2 H(t) · r/(1 − t·r)` on `(0, 1)` (with
`0 ≤ r < 1`). Then `(1 − r)² H(0) ≤ H(1) ≤ (1 − r)⁻² H(0)`.

Proof: monotonicity trick that avoids `log`. The auxiliary function
`φ(t) := (1 − t·r)² · H(t)` has `φ'(t) ≤ 0` on `(0, 1)` (using
`(1 − t·r) H'(t) ≤ 2r H(t)` derived from the hypothesis), hence
`φ` is antitone on `[0, 1]` and `φ(1) ≤ φ(0)` gives
`(1 − r)² H(1) ≤ H(0)`. Symmetrically, `ψ(t) := H(t) / (1 − t·r)²`
is monotone, giving the lower bound. -/
lemma multiplicative_path_bound_from_log_ode
    {H : ℝ → ℝ} {r : ℝ}
    (hr_nn : 0 ≤ r) (hr_lt_one : r < 1)
    (hH_nn : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ H t)
    (hH_cont : ContinuousOn H (Set.Icc (0:ℝ) 1))
    (hH_deriv : ∀ t ∈ Set.Ioo (0:ℝ) 1, ∃ H', HasDerivAt H H' t ∧
                |H'| ≤ 2 * H t * (r / (1 - t * r))) :
    (1 - r) ^ 2 * H 0 ≤ H 1 ∧ H 1 ≤ (1 - r) ^ (-2 : ℝ) * H 0 := by
  -- Positivity setup.
  have h1r_pos : (0 : ℝ) < 1 - r := by linarith
  have h1tr_pos : ∀ t ∈ Set.Icc (0:ℝ) 1, (0 : ℝ) < 1 - t * r := by
    intro t ⟨h0, h1⟩; nlinarith
  have hsq_pos : ∀ t ∈ Set.Icc (0:ℝ) 1, (0 : ℝ) < (1 - t * r) ^ 2 :=
    fun t ht => pow_pos (h1tr_pos t ht) 2
  -- Shared derivative computations.
  -- d/dt (1 - t·r) = -r.
  have h_1tr_deriv : ∀ s : ℝ, HasDerivAt (fun u : ℝ => 1 - u * r) (-r) s := by
    intro s
    have h_id_mul : HasDerivAt (fun u : ℝ => u * r) r s := by
      simpa using (hasDerivAt_id s).mul_const r
    simpa using h_id_mul.const_sub 1
  -- d/dt (1 - t·r)² = -2r·(1 - t·r).
  have hsq_deriv : ∀ s : ℝ,
      HasDerivAt (fun u : ℝ => (1 - u * r) ^ 2) (-(2 * r * (1 - s * r))) s := by
    intro s
    have h := (h_1tr_deriv s).pow 2
    convert h using 1
    push_cast; ring
  -- Useful interior-of-Icc identity.
  have h_interior : interior (Set.Icc (0:ℝ) 1) = Set.Ioo 0 1 := interior_Icc
  -- ── Upper bound: H 1 ≤ (1 - r)⁻² · H 0 via φ(t) = (1 - t·r)² · H(t). ──
  have h_upper : H 1 ≤ (1 - r) ^ (-2 : ℝ) * H 0 := by
    set φ : ℝ → ℝ := fun t => (1 - t * r) ^ 2 * H t with hφ_def
    -- φ continuous on [0, 1].
    have hφ_cont : ContinuousOn φ (Set.Icc 0 1) :=
      (Continuous.continuousOn (by continuity)).mul hH_cont
    -- φ differentiable on (0, 1) with deriv ≤ 0.
    have hφ_diff_deriv : ∀ t ∈ Set.Ioo (0:ℝ) 1,
        DifferentiableAt ℝ φ t ∧ deriv φ t ≤ 0 := by
      intro t ht
      obtain ⟨H', hH'_deriv, hH'_bd⟩ := hH_deriv t ht
      have hφ_deriv_at :
          HasDerivAt φ (-(2 * r * (1 - t * r)) * H t + (1 - t * r) ^ 2 * H') t :=
        (hsq_deriv t).mul hH'_deriv
      refine ⟨hφ_deriv_at.differentiableAt, ?_⟩
      rw [hφ_deriv_at.deriv]
      -- Bound: -(2r(1-tr)) H t + (1-tr)² H' ≤ 0.
      have ht_Icc : t ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
      have h_1tr := h1tr_pos t ht_Icc
      have h_H_nn := hH_nn t ht_Icc
      have h_H'_le : H' ≤ 2 * H t * (r / (1 - t * r)) :=
        (le_abs_self H').trans hH'_bd
      have h_step : (1 - t * r) * H' ≤ 2 * H t * r := by
        have hmul := mul_le_mul_of_nonneg_left h_H'_le (le_of_lt h_1tr)
        calc (1 - t * r) * H'
            ≤ (1 - t * r) * (2 * H t * (r / (1 - t * r))) := hmul
          _ = 2 * H t * r := by field_simp
      nlinarith [h_step, h_1tr, h_H_nn, hr_nn,
        mul_le_mul_of_nonneg_left h_step (le_of_lt h_1tr)]
    have hφ_diff : DifferentiableOn ℝ φ (interior (Set.Icc (0:ℝ) 1)) := by
      rw [h_interior]
      intro t ht
      exact (hφ_diff_deriv t ht).1.differentiableWithinAt
    have hφ_nonpos : ∀ t ∈ interior (Set.Icc (0:ℝ) 1), deriv φ t ≤ 0 := by
      rw [h_interior]; intro t ht; exact (hφ_diff_deriv t ht).2
    have h_anti : AntitoneOn φ (Set.Icc (0:ℝ) 1) :=
      antitoneOn_of_deriv_nonpos (convex_Icc 0 1) hφ_cont hφ_diff hφ_nonpos
    have h_phi_le : φ 1 ≤ φ 0 :=
      h_anti (Set.left_mem_Icc.mpr zero_le_one)
             (Set.right_mem_Icc.mpr zero_le_one) zero_le_one
    have hφ_0 : φ 0 = H 0 := by simp [φ]
    have hφ_1 : φ 1 = (1 - r) ^ 2 * H 1 := by simp [φ]
    rw [hφ_0, hφ_1] at h_phi_le
    -- h_phi_le : (1 - r) ^ 2 * H 1 ≤ H 0. Divide by (1 - r)² > 0.
    have h_sq_pos : (0 : ℝ) < (1 - r) ^ 2 := by positivity
    have h_div : H 1 ≤ H 0 / (1 - r) ^ 2 := by
      rw [le_div_iff₀ h_sq_pos]; linarith
    have h_rpow_eq : (1 - r) ^ (-2 : ℝ) * H 0 = H 0 / (1 - r) ^ 2 := by
      rw [Real.rpow_neg (le_of_lt h1r_pos), Real.rpow_two]
      field_simp
    rw [h_rpow_eq]; exact h_div
  -- ── Lower bound: (1 - r)² · H 0 ≤ H 1 via ψ(t) = H(t) / (1 - t·r)². ──
  have h_lower : (1 - r) ^ 2 * H 0 ≤ H 1 := by
    set ψ : ℝ → ℝ := fun t => H t / (1 - t * r) ^ 2 with hψ_def
    -- ψ continuous on [0, 1].
    have hψ_cont : ContinuousOn ψ (Set.Icc 0 1) := by
      refine ContinuousOn.div hH_cont (Continuous.continuousOn (by continuity)) ?_
      intro t ht; exact ne_of_gt (hsq_pos t ht)
    -- ψ differentiable on (0, 1) with deriv ≥ 0.
    have hψ_diff_deriv : ∀ t ∈ Set.Ioo (0:ℝ) 1,
        DifferentiableAt ℝ ψ t ∧ 0 ≤ deriv ψ t := by
      intro t ht
      obtain ⟨H', hH'_deriv, hH'_bd⟩ := hH_deriv t ht
      have ht_Icc : t ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
      have hsq_ne_t : (1 - t * r) ^ 2 ≠ 0 := ne_of_gt (hsq_pos t ht_Icc)
      have hψ_deriv_at : HasDerivAt ψ
          ((H' * (1 - t * r) ^ 2 - H t * (-(2 * r * (1 - t * r)))) /
            ((1 - t * r) ^ 2) ^ 2) t :=
        hH'_deriv.div (hsq_deriv t) hsq_ne_t
      refine ⟨hψ_deriv_at.differentiableAt, ?_⟩
      rw [hψ_deriv_at.deriv]
      -- Show the quotient is ≥ 0: numerator ≥ 0 and denominator > 0.
      have h_1tr := h1tr_pos t ht_Icc
      have h_H_nn := hH_nn t ht_Icc
      have h_H'_ge : -(2 * H t * (r / (1 - t * r))) ≤ H' := by
        have := neg_abs_le H'; linarith
      have h_step : -(2 * H t * r) ≤ (1 - t * r) * H' := by
        have hmul := mul_le_mul_of_nonneg_left h_H'_ge (le_of_lt h_1tr)
        have h_eq : (1 - t * r) * (-(2 * H t * (r / (1 - t * r)))) = -(2 * H t * r) := by
          have h_ne : (1 - t * r) ≠ 0 := ne_of_gt h_1tr
          field_simp
        linarith
      apply div_nonneg _ (sq_nonneg _)
      nlinarith [h_step, h_1tr, h_H_nn, hr_nn,
        mul_le_mul_of_nonneg_left h_step (le_of_lt h_1tr)]
    have hψ_diff : DifferentiableOn ℝ ψ (interior (Set.Icc (0:ℝ) 1)) := by
      rw [h_interior]
      intro t ht
      exact (hψ_diff_deriv t ht).1.differentiableWithinAt
    have hψ_nonneg : ∀ t ∈ interior (Set.Icc (0:ℝ) 1), 0 ≤ deriv ψ t := by
      rw [h_interior]; intro t ht; exact (hψ_diff_deriv t ht).2
    have h_mono : MonotoneOn ψ (Set.Icc (0:ℝ) 1) :=
      monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hψ_cont hψ_diff hψ_nonneg
    have h_psi_le : ψ 0 ≤ ψ 1 :=
      h_mono (Set.left_mem_Icc.mpr zero_le_one)
             (Set.right_mem_Icc.mpr zero_le_one) zero_le_one
    have hψ_0 : ψ 0 = H 0 := by simp [ψ]
    have hψ_1 : ψ 1 = H 1 / (1 - r) ^ 2 := by simp [ψ]
    rw [hψ_0, hψ_1] at h_psi_le
    -- h_psi_le : H 0 ≤ H 1 / (1 - r) ^ 2. Multiply by (1 - r)² ≥ 0.
    have h_sq_pos : (0 : ℝ) < (1 - r) ^ 2 := by positivity
    rw [le_div_iff₀ h_sq_pos] at h_psi_le
    linarith
  exact ⟨h_lower, h_upper⟩

namespace LHSCB

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V]

/-- **Chain rule along the affine segment.** For an LHSCB `f` and any
direction `h`, the map `s ↦ hess f.f K (u₀ + s·(u−u₀)) h` (i.e. the
Hessian quadratic form along the segment in direction `h`) is
differentiable at any `t ∈ (0, 1)` with derivative
`iteratedFDerivWithin ℝ 3 f.f (interior K) (u₀ + t·(u−u₀)) ![u−u₀, h, h]`.

Proof: `iteratedFDerivWithin ℝ 2 f.f (interior K)` is `C¹` at `γ t ∈
interior K` (from `f.contDiff₃` + `ContDiffWithinAt.iteratedFDerivWithin_right`,
then upgraded to `ContDiffAt` since `interior K` is open). Composing
its Fréchet derivative with the affine path `γ` (chain rule
`HasFDerivAt.comp_hasDerivAt`) gives the derivative of
`s ↦ iteratedFDerivWithin ℝ 2 f.f (interior K) (γ s)`. Composing once
more with the continuous-linear evaluation `M ↦ M (fun _ => h)`
(`ContinuousMultilinearMap.apply`) yields the scalar derivative. The
identification with `iteratedFDerivWithin ℝ 3 …` follows from
`iteratedFDerivWithin_succ_apply_left` (with `n = 2`) and
`fderivWithin_of_isOpen` on the open `interior K`. -/
lemma hess_path_has_deriv_at {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {K : Set V} {ν : ℕ} {d : ℕ∞}
    (f : LHSCB V K ν d) (hK_convex : Convex ℝ K)
    (u₀ u h : V) (hu₀ : u₀ ∈ interior K) (hu : u ∈ interior K)
    (t : ℝ) (ht : t ∈ Set.Ioo (0:ℝ) 1) :
    HasDerivAt (fun s => hess f.f K (u₀ + s • (u - u₀)) h)
      (iteratedFDerivWithin ℝ 3 f.f (interior K)
        (u₀ + t • (u - u₀)) ![u - u₀, h, h]) t := by
  set γ : ℝ → V := fun s => u₀ + s • (u - u₀) with hγ_def
  -- (1) `γ` has derivative `u - u₀` at every point.
  have hγ_deriv : HasDerivAt γ (u - u₀) t := by
    have h_smul : HasDerivAt (fun s : ℝ => s • (u - u₀)) (u - u₀) t := by
      simpa using (hasDerivAt_id t).smul_const (u - u₀)
    simpa [γ] using h_smul.const_add u₀
  -- (2) `γ t ∈ interior K`.
  have ht_Icc : t ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hγt_in : γ t ∈ interior K :=
    segment_in_interior hK_convex u₀ hu₀ u hu t ht_Icc
  -- (3) `iteratedFDerivWithin ℝ 2 f.f (interior K)` is differentiable at `γ t`.
  have hf_wat : ContDiffWithinAt ℝ 3 f.f (interior K) (γ t) :=
    f.contDiff₃.contDiffWithinAt hγt_in
  have h_iter_wat :
      ContDiffWithinAt ℝ 1 (iteratedFDerivWithin ℝ 2 f.f (interior K))
        (interior K) (γ t) :=
    hf_wat.iteratedFDerivWithin_right isOpen_interior.uniqueDiffOn
      (by norm_num : (1 : WithTop ℕ∞) + 2 ≤ 3) hγt_in
  have h_iter_at :
      ContDiffAt ℝ 1 (iteratedFDerivWithin ℝ 2 f.f (interior K)) (γ t) :=
    h_iter_wat.contDiffAt (isOpen_interior.mem_nhds hγt_in)
  have h_iter_diff :
      DifferentiableAt ℝ (iteratedFDerivWithin ℝ 2 f.f (interior K)) (γ t) :=
    h_iter_at.differentiableAt_one
  -- (4) Chain rule: HasDerivAt of `iteratedFDerivWithin 2 f.f K ∘ γ` at t.
  set L : V →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) ℝ :=
    fderiv ℝ (iteratedFDerivWithin ℝ 2 f.f (interior K)) (γ t) with hL_def
  have h_fd_at :
      HasFDerivAt (iteratedFDerivWithin ℝ 2 f.f (interior K)) L (γ t) :=
    h_iter_diff.hasFDerivAt
  have h_iter_γ_deriv :
      HasDerivAt (fun s => iteratedFDerivWithin ℝ 2 f.f (interior K) (γ s))
        (L (u - u₀)) t :=
    h_fd_at.comp_hasDerivAt t hγ_deriv
  -- (5) Compose with the continuous-linear eval `ev : CMM →L[ℝ] ℝ`.
  set ev : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) ℝ →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => V) ℝ (fun _ => h) with hev_def
  have h_hess_γ_deriv :
      HasDerivAt (fun s => ev (iteratedFDerivWithin ℝ 2 f.f (interior K) (γ s)))
        (ev (L (u - u₀))) t :=
    (ev.hasFDerivAt (x := iteratedFDerivWithin ℝ 2 f.f (interior K)
      (γ t))).comp_hasDerivAt t h_iter_γ_deriv
  -- (6) Identify `ev (L (u - u₀))` with `iteratedFDerivWithin ℝ 3 ... ![u-u₀, h, h]`.
  have h_tail_eq :
      Fin.tail (![u - u₀, h, h] : Fin 3 → V) = (fun _ : Fin 2 => h) := by
    funext i; fin_cases i <;> rfl
  have h_deriv_eq :
      iteratedFDerivWithin ℝ 3 f.f (interior K) (γ t) ![u - u₀, h, h]
        = ev (L (u - u₀)) := by
    -- `iteratedFDerivWithin_succ_apply_left` is `rfl` (for `n = 2`), unfolding
    -- the LHS to `fderivWithin … (m 0) (Fin.tail m)`; `(m 0) = u - u₀` is
    -- defeq via Fin.cases reduction.
    show fderivWithin ℝ (iteratedFDerivWithin ℝ 2 f.f (interior K))
          (interior K) (γ t) (u - u₀)
          (Fin.tail (![u - u₀, h, h] : Fin 3 → V)) = ev (L (u - u₀))
    rw [fderivWithin_of_isOpen isOpen_interior hγt_in, h_tail_eq]
    rfl
  rw [h_deriv_eq]
  exact h_hess_γ_deriv

/-- **Abstract polarization of cubic self-concordance.** For a symmetric
continuous trilinear `T` and a symmetric PSD continuous bilinear `Q` on
a normed real vector space, if `T` satisfies the diagonal bound
`|T(w, w, w)| ≤ 2 (√Q(w, w))³` for every `w`, then it satisfies the
polarized bound `|T(v, h, h)| ≤ 2·Q(h, h)·√Q(v, v)` for every `v, h`.

Pure multilinear-algebra statement: no analysis, no LHSCB. Proof
strategy (Nesterov–Nemirovski): apply the diagonal bound at the
direction `h + λ·v`, expand the cubic in `λ` (using full symmetry of
`T` to combine like terms), extract the coefficient of `λ¹` (which is
`3·T(v, h, h)`), bound it using the diagonal at `v` and Cauchy–Schwarz
on `Q`. Optimize over `λ`. -/
private lemma sc_polarized_abstract
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => V) ℝ)
    (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) ℝ)
    (hT_sym : ∀ (m : Fin 3 → V) (σ : Equiv.Perm (Fin 3)), T (m ∘ σ) = T m)
    (hQ_sym : ∀ a b : V, Q ![a, b] = Q ![b, a])
    (hQ_psd : ∀ w : V, 0 ≤ Q (fun _ => w))
    (hT_diag : ∀ w : V, |T (fun _ => w)| ≤ 2 * (Real.sqrt (Q (fun _ => w))) ^ 3)
    (v h : V) :
    |T ![v, h, h]| ≤ 2 * Q (fun _ => h) * Real.sqrt (Q (fun _ => v)) := by
  sorry

/-- **Symmetry of the 3rd iterated Fréchet derivative.** For a `C³`
function on an open set, the iterated Fréchet derivative
`iteratedFDerivWithin ℝ 3 f s x` is symmetric under permutations of
its three arguments. (Pure Mathlib statement; the Schwarz theorem
extension to third derivatives. Follows from the recursive structure
of `iteratedFDeriv` plus `IsSymmSndFDerivWithinAt` applied to
`fderiv f`.) -/
private lemma iteratedFDerivWithin_3_perm_invariant
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : V → ℝ} {s : Set V} (hs : IsOpen s) (hf : ContDiffOn ℝ 3 f s)
    {x : V} (hx : x ∈ s) (m : Fin 3 → V) (σ : Equiv.Perm (Fin 3)) :
    iteratedFDerivWithin ℝ 3 f s x (m ∘ σ) = iteratedFDerivWithin ℝ 3 f s x m := by
  sorry

/-- **Polarized self-concordance bound.** Off-diagonal cubic-form
bound: `|D³f(x)[v, h, h]| ≤ 2 · D²f(x)[h, h] · √D²f(x)[v, v]` for any
directions `v, h` at any interior point `x`.

Now proved as a trivial application of the abstract polarization
(`sc_polarized_abstract`) with `T := iteratedFDerivWithin ℝ 3 f.f
(interior K) x` and `Q := iteratedFDerivWithin ℝ 2 f.f (interior K) x`.
Symmetry of `T` comes from `iteratedFDerivWithin_3_perm_invariant`,
symmetry of `Q` from Mathlib's
`IsSymmSndFDerivWithinAt.iteratedFDerivWithin_cons`, PSD of `Q` from
`f.self_concordant_hessian_nonneg`, and diagonal SC from
`f.self_concordant_abs_third`. -/
lemma self_concordant_polarized {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {K : Set V} {ν : ℕ} {d : ℕ∞}
    (f : LHSCB V K ν d) (x : V) (hx : x ∈ interior K) (v h : V) :
    |iteratedFDerivWithin ℝ 3 f.f (interior K) x ![v, h, h]| ≤
      2 * iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => h) *
        Real.sqrt (iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => v)) := by
  -- Apply abstract polarization with T, Q as the iterated derivatives.
  set T := iteratedFDerivWithin ℝ 3 f.f (interior K) x with hT_def
  set Q := iteratedFDerivWithin ℝ 2 f.f (interior K) x with hQ_def
  have hf_C3 : ContDiffOn ℝ 3 f.f (interior K) := f.contDiff₃
  -- Symmetry of `T`: `iteratedFDerivWithin_3_perm_invariant`.
  have hT_sym : ∀ (m : Fin 3 → V) (σ : Equiv.Perm (Fin 3)), T (m ∘ σ) = T m :=
    fun m σ => iteratedFDerivWithin_3_perm_invariant isOpen_interior hf_C3 hx m σ
  -- Symmetry of `Q` (single transposition): from
  -- `IsSymmSndFDerivWithinAt.iteratedFDerivWithin_cons`.
  have hQ_sym : ∀ a b : V, Q ![a, b] = Q ![b, a] := by
    intro a b
    have h_C2_at : ContDiffAt ℝ 2 f.f x := by
      have : ContDiffOn ℝ 2 f.f (interior K) :=
        hf_C3.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
      exact (this.contDiffWithinAt hx).contDiffAt (isOpen_interior.mem_nhds hx)
    have h_symm_at : IsSymmSndFDerivAt ℝ f.f x :=
      h_C2_at.isSymmSndFDerivAt (by simp : minSmoothness ℝ 2 ≤ (2 : WithTop ℕ∞))
    have h_symm : IsSymmSndFDerivWithinAt ℝ f.f (interior K) x :=
      h_symm_at.isSymmSndFDerivWithinAt h_C2_at isOpen_interior.uniqueDiffOn hx
    exact h_symm.iteratedFDerivWithin_cons isOpen_interior.uniqueDiffOn hx
  -- PSD of Q.
  have hQ_psd : ∀ w : V, 0 ≤ Q (fun _ => w) :=
    fun w => f.self_concordant_hessian_nonneg x hx w
  -- Diagonal SC.
  have hT_diag : ∀ w : V, |T (fun _ => w)| ≤ 2 * (Real.sqrt (Q (fun _ => w))) ^ 3 :=
    fun w => f.self_concordant_abs_third x hx w
  -- Apply.
  exact sc_polarized_abstract T Q hT_sym hQ_sym hQ_psd hT_diag v h

/-- **Lemma 1.** Diagonal Dikin metric bound along the segment.
For `t ∈ [0, 1]` and `r = √(hess f u₀ (u−u₀)) < 1`, the local norm of
the displacement at `u₀ + t·(u−u₀)` is bounded by `r/(1 − tr)`.

Proved by feeding the chain rule (`hess_path_has_deriv_at` with `h := u − u₀`)
and the diagonal SC bound (`self_concordant_abs_third`) into the abstract
ODE integrator `local_norm_path_bound_from_diagonal_ode`. -/
lemma dikin_path_metric_bound {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {K : Set V} {ν : ℕ} {d : ℕ∞}
    (f : LHSCB V K ν d) (hK_convex : Convex ℝ K)
    (u₀ u : V) (hu₀ : u₀ ∈ interior K) (hu : u ∈ interior K)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1)
    (r : ℝ) (hr_pos : 0 ≤ r) (hr_lt_one : r < 1)
    (h_in_ball : hess f.f K u₀ (u - u₀) ≤ r ^ 2) :
    local_norm f.f K (u₀ + t • (u - u₀)) (u - u₀) ≤ r / (1 - t * r) := by
  set γ : ℝ → V := fun t => u₀ + t • (u - u₀) with hγ_def
  set a : ℝ → ℝ := fun t => hess f.f K (γ t) (u - u₀) with ha_def
  have h_in : ∀ s ∈ Set.Icc (0:ℝ) 1, γ s ∈ interior K :=
    segment_in_interior hK_convex u₀ hu₀ u hu
  have ha_nn : ∀ s ∈ Set.Icc (0:ℝ) 1, 0 ≤ a s := fun s hs =>
    f.self_concordant_hessian_nonneg (γ s) (h_in s hs) (u - u₀)
  -- `a` is continuous on `[0, 1]`: `iteratedFDerivWithin 2 f.f (interior K)` is
  -- continuous on `interior K` (from `f.contDiff₃`), composed with the
  -- continuous CMM evaluation and the continuous affine path `γ`.
  have ha_cont : ContinuousOn a (Set.Icc (0:ℝ) 1) := by
    have h_iter_cont :
        ContinuousOn (iteratedFDerivWithin ℝ 2 f.f (interior K)) (interior K) :=
      f.contDiff₃.continuousOn_iteratedFDerivWithin (by norm_num)
        isOpen_interior.uniqueDiffOn
    have h_eval_cont :
        Continuous (fun M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) ℝ =>
          M (fun _ => u - u₀)) :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => V) ℝ
        (fun _ => u - u₀)).continuous
    have h_hess_cont :
        ContinuousOn (fun x : V => hess f.f K x (u - u₀)) (interior K) :=
      h_eval_cont.comp_continuousOn h_iter_cont
    have hγ_cont : Continuous γ := by
      show Continuous (fun s : ℝ => u₀ + s • (u - u₀))
      continuity
    exact h_hess_cont.comp hγ_cont.continuousOn h_in
  have ha_0 : a 0 ≤ r ^ 2 := by
    show hess f.f K (γ 0) (u - u₀) ≤ r ^ 2
    have h_γ0 : γ 0 = u₀ := by simp [γ]
    rw [h_γ0]; exact h_in_ball
  have ha_deriv : ∀ s ∈ Set.Ioo (0:ℝ) 1, ∃ a', HasDerivAt a a' s ∧
                  |a'| ≤ 2 * (Real.sqrt (a s)) ^ 3 := by
    intro s hs
    refine ⟨_, hess_path_has_deriv_at f hK_convex u₀ u (u - u₀) hu₀ hu s hs, ?_⟩
    -- Identify `![u-u₀, u-u₀, u-u₀]` with the constant function and apply diagonal SC.
    have h_diag :
        (![u - u₀, u - u₀, u - u₀] : Fin 3 → V) = (fun _ => u - u₀) := by
      funext i; fin_cases i <;> rfl
    rw [h_diag]
    have hs_Icc : s ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
    exact f.self_concordant_abs_third (γ s) (h_in s hs_Icc) (u - u₀)
  have h_bd := local_norm_path_bound_from_diagonal_ode ha_nn ha_cont ha_0 hr_pos hr_lt_one ha_deriv
  show Real.sqrt (a t) ≤ r / (1 - t * r)
  exact h_bd t ht

/-- **Lemma 2.** Polarized self-concordance bound along the segment:
the derivative of `t ↦ hess f (u₀ + t·(u−u₀)) h` is bounded by
`2 · hess f (·) h · local_norm f (·) (u−u₀)`.

Proved by combining the chain rule (`hess_path_has_deriv_at`) with the
off-diagonal SC bound (`self_concordant_polarized`). -/
lemma path_hess_deriv_bound {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {K : Set V} {ν : ℕ} {d : ℕ∞}
    (f : LHSCB V K ν d) (hK_convex : Convex ℝ K)
    (u₀ u h : V) (hu₀ : u₀ ∈ interior K) (hu : u ∈ interior K)
    (t : ℝ) (ht : t ∈ Set.Ioo (0:ℝ) 1) :
    ∃ H', HasDerivAt (fun s => hess f.f K (u₀ + s • (u - u₀)) h) H' t ∧
          |H'| ≤ 2 * hess f.f K (u₀ + t • (u - u₀)) h *
                 local_norm f.f K (u₀ + t • (u - u₀)) (u - u₀) := by
  set γ : ℝ → V := fun t => u₀ + t • (u - u₀) with hγ_def
  refine ⟨_, hess_path_has_deriv_at f hK_convex u₀ u h hu₀ hu t ht, ?_⟩
  have ht_Icc : t ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have h_in : γ t ∈ interior K :=
    segment_in_interior hK_convex u₀ hu₀ u hu t ht_Icc
  show |iteratedFDerivWithin ℝ 3 f.f (interior K) (γ t) ![u - u₀, h, h]| ≤
       2 * iteratedFDerivWithin ℝ 2 f.f (interior K) (γ t) (fun _ => h) *
         Real.sqrt (iteratedFDerivWithin ℝ 2 f.f (interior K) (γ t)
           (fun _ => u - u₀))
  exact f.self_concordant_polarized (γ t) h_in (u - u₀) h

/-- **Lemma 3.** Integrating Lemma 2 against Lemma 1 from `0` to `1`:
`(1−r)² · hess f u₀ h ≤ hess f u h ≤ (1−r)⁻² · hess f u₀ h`.

Proved by combining Lemma 2 (derivative bound) with Lemma 1 (metric
bound) to satisfy the hypothesis of `multiplicative_path_bound_from_log_ode`. -/
lemma path_hess_integrated_bound {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {K : Set V} {ν : ℕ} {d : ℕ∞}
    (f : LHSCB V K ν d) (hK_convex : Convex ℝ K)
    (u₀ u h : V) (hu₀ : u₀ ∈ interior K) (hu : u ∈ interior K)
    (r : ℝ) (hr_pos : 0 ≤ r) (hr_lt_one : r < 1)
    (h_in_ball : hess f.f K u₀ (u - u₀) ≤ r ^ 2) :
    (1 - r) ^ 2 * hess f.f K u₀ h ≤ hess f.f K u h ∧
    hess f.f K u h ≤ (1 - r) ^ (-2 : ℝ) * hess f.f K u₀ h := by
  set γ : ℝ → V := fun t => u₀ + t • (u - u₀) with hγ_def
  set H : ℝ → ℝ := fun t => hess f.f K (γ t) h with hH_def
  have h_in : ∀ s ∈ Set.Icc (0:ℝ) 1, γ s ∈ interior K :=
    segment_in_interior hK_convex u₀ hu₀ u hu
  have hH_nn : ∀ s ∈ Set.Icc (0:ℝ) 1, 0 ≤ H s := fun s hs =>
    f.self_concordant_hessian_nonneg (γ s) (h_in s hs) h
  -- H is continuous on [0, 1]: `iteratedFDerivWithin ℝ 2 f.f (interior K)` is
  -- continuous on `interior K` (from `f.contDiff₃` plus
  -- `ContDiffOn.continuousOn_iteratedFDerivWithin`), composed with the
  -- continuous evaluation `M ↦ M (fun _ => h)` and the continuous affine path γ
  -- (which maps `[0, 1]` into `interior K` by `segment_in_interior`).
  have hH_cont : ContinuousOn H (Set.Icc (0:ℝ) 1) := by
    have h_iter_cont :
        ContinuousOn (iteratedFDerivWithin ℝ 2 f.f (interior K)) (interior K) :=
      f.contDiff₃.continuousOn_iteratedFDerivWithin (by norm_num)
        isOpen_interior.uniqueDiffOn
    have h_eval_cont :
        Continuous (fun M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) ℝ =>
          M (fun _ => h)) :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => V) ℝ
        (fun _ => h)).continuous
    have h_hess_cont : ContinuousOn (fun x : V => hess f.f K x h) (interior K) :=
      h_eval_cont.comp_continuousOn h_iter_cont
    have hγ_cont : Continuous γ := by
      show Continuous (fun s : ℝ => u₀ + s • (u - u₀))
      continuity
    exact h_hess_cont.comp hγ_cont.continuousOn h_in
  have hH_deriv : ∀ s ∈ Set.Ioo (0:ℝ) 1, ∃ H', HasDerivAt H H' s ∧
                  |H'| ≤ 2 * H s * (r / (1 - s * r)) := by
    intro s hs
    obtain ⟨H', hH'_deriv, hH'_bd⟩ :=
      f.path_hess_deriv_bound hK_convex u₀ u h hu₀ hu s hs
    refine ⟨H', hH'_deriv, ?_⟩
    have hs_Icc : s ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
    have h_local := f.dikin_path_metric_bound hK_convex u₀ u hu₀ hu s hs_Icc r
      hr_pos hr_lt_one h_in_ball
    have h_H_nn := hH_nn s hs_Icc
    calc |H'|
        ≤ 2 * H s * local_norm f.f K (γ s) (u - u₀) := hH'_bd
      _ ≤ 2 * H s * (r / (1 - s * r)) := by
          have h_factor_nn : 0 ≤ 2 * H s := by positivity
          exact mul_le_mul_of_nonneg_left h_local h_factor_nn
  have h_result :=
    multiplicative_path_bound_from_log_ode hr_pos hr_lt_one hH_nn hH_cont hH_deriv
  have hH_0 : H 0 = hess f.f K u₀ h := by
    show hess f.f K (γ 0) h = hess f.f K u₀ h
    congr 1; simp [γ]
  have hH_1 : H 1 = hess f.f K u h := by
    show hess f.f K (γ 1) h = hess f.f K u h
    congr 1
    show u₀ + (1 : ℝ) • (u - u₀) = u
    rw [one_smul]; abel
  rw [hH_0, hH_1] at h_result
  exact h_result

omit [CompleteSpace V] in
/-- **Dikin-ball Hessian Lipschitz bound (paper §6.3 Lemma 16 step (i)).**
For `u, u₀ ∈ int K` such that the SC-norm displacement
`r² := ⟨u − u₀, ∇²f(u₀)(u − u₀)⟩` is less than `1`, the Hessian
quadratic form satisfies the multiplicative bound
`(1 − r)² ⟨h, ∇²f(u₀) h⟩ ≤ ⟨h, ∇²f(u) h⟩ ≤ (1 − r)⁻² ⟨h, ∇²f(u₀) h⟩`
for every direction `h`. The constants depend only on `r` — not on
`u₀`, `K`, or the LHSCB barrier parameter `ν` — which is what makes
the LHSCB Newton–Kantorovich basin radius an *absolute* constant.

Now a thin wrapper around `path_hess_integrated_bound`; the analytic
content lives in the four scaffold lemmas above. -/
theorem hessian_dikin_bound {K : Set V} {ν : ℕ} {d : ℕ∞}
    (f : LHSCB V K ν d) (hK_convex : Convex ℝ K)
    (u₀ : V) (hu₀ : u₀ ∈ interior K)
    (u : V) (hu : u ∈ interior K)
    (r : ℝ) (hr_pos : 0 ≤ r) (hr_lt_one : r < 1)
    (h_in_ball :
      iteratedFDerivWithin ℝ 2 f.f (interior K) u₀ (fun _ => u - u₀) ≤ r ^ 2) :
    ∀ h : V,
      (1 - r) ^ 2 *
          iteratedFDerivWithin ℝ 2 f.f (interior K) u₀ (fun _ => h) ≤
        iteratedFDerivWithin ℝ 2 f.f (interior K) u (fun _ => h) ∧
      iteratedFDerivWithin ℝ 2 f.f (interior K) u (fun _ => h) ≤
        (1 - r) ^ (-2 : ℝ) *
          iteratedFDerivWithin ℝ 2 f.f (interior K) u₀ (fun _ => h) := by
  intro h
  exact path_hess_integrated_bound f hK_convex u₀ u h hu₀ hu r hr_pos hr_lt_one h_in_ball

/-- **Sum of LHSCBs.** A `ν₁`-LHSCB on `K₁` plus a `ν₂`-LHSCB on `K₂`
is a `(ν₁+ν₂)`-LHSCB on `K₁ ∩ K₂` of smoothness `min d₁ d₂`. -/
noncomputable def add {K₁ K₂ : Set V} {ν₁ ν₂ : ℕ} {d₁ d₂ : ℕ∞}
    (f : LHSCB V K₁ ν₁ d₁) (g : LHSCB V K₂ ν₂ d₂) :
    LHSCB V (K₁ ∩ K₂) (ν₁ + ν₂) (min d₁ d₂) where
  hd_ge := le_min f.hd_ge g.hd_ge
  convex_K := f.convex_K.inter g.convex_K
  f := fun v => f.f v + g.f v
  contDiff := by
    have hmin1 : (min d₁ d₂ : WithTop ℕ∞) ≤ (d₁ : WithTop ℕ∞) := by
      exact_mod_cast min_le_left d₁ d₂
    have hmin2 : (min d₁ d₂ : WithTop ℕ∞) ≤ (d₂ : WithTop ℕ∞) := by
      exact_mod_cast min_le_right d₁ d₂
    rw [interior_inter]
    exact ContDiffOn.add
      ((f.contDiff.of_le hmin1).mono Set.inter_subset_left)
      ((g.contDiff.of_le hmin2).mono Set.inter_subset_right)
  self_concordant := by
    -- Nesterov's self-concordant sum theorem. The iterated derivatives
    -- of `f.f + g.f` are sums of the individual iterated derivatives
    -- (additivity), and the SC bound is closed under the algebraic
    -- combination via `sc_sum_ineq`.
    intro x hx h
    have hx' : x ∈ interior K₁ ∩ interior K₂ := by
      rw [interior_inter] at hx; exact hx
    obtain ⟨hx₁, hx₂⟩ := hx'
    have hf_C3_at : ContDiffAt ℝ 3 f.f x :=
      f.contDiff₃.contDiffAt (isOpen_interior.mem_nhds hx₁)
    have hg_C3_at : ContDiffAt ℝ 3 g.f x :=
      g.contDiff₃.contDiffAt (isOpen_interior.mem_nhds hx₂)
    -- Identify `iteratedFDerivWithin n (f.f + g.f) (interior (K₁ ∩ K₂))`
    -- with `iteratedFDeriv n f.f + iteratedFDeriv n g.f` via `_of_isOpen`
    -- and `iteratedFDeriv_add_apply` (the `fun v => f v + g v` form).
    have hx_inter : x ∈ interior (K₁ ∩ K₂) := by
      rw [interior_inter]; exact ⟨hx₁, hx₂⟩
    have h_open_inter : IsOpen (interior (K₁ ∩ K₂)) := isOpen_interior
    have h_eq_n : ∀ n : ℕ, n ≤ 3 →
        iteratedFDerivWithin ℝ n (fun v => f.f v + g.f v) (interior (K₁ ∩ K₂)) x =
          iteratedFDerivWithin ℝ n f.f (interior K₁) x +
            iteratedFDerivWithin ℝ n g.f (interior K₂) x := by
      intro n hn
      have hn' : (n : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hn
      rw [iteratedFDerivWithin_of_isOpen _ h_open_inter hx_inter,
          iteratedFDerivWithin_of_isOpen _ isOpen_interior hx₁,
          iteratedFDerivWithin_of_isOpen _ isOpen_interior hx₂]
      exact iteratedFDeriv_add_apply (hf_C3_at.of_le hn') (hg_C3_at.of_le hn')
    have h_eq2 := h_eq_n 2 (by norm_num)
    have h_eq3 := h_eq_n 3 (by norm_num)
    -- SC bounds for f and g.
    have hf_sc := f.self_concordant x hx₁ h
    have hg_sc := g.self_concordant x hx₂ h
    -- Hessian non-negativity for f and g.
    have hf_nn := f.self_concordant_hessian_nonneg x hx₁ h
    have hg_nn := g.self_concordant_hessian_nonneg x hx₂ h
    -- Combine via sc_sum_ineq.
    rw [h_eq2, h_eq3, ContinuousMultilinearMap.add_apply,
      ContinuousMultilinearMap.add_apply]
    exact sc_sum_ineq hf_nn hg_nn hf_sc hg_sc
  log_homog := by
    rintro x hx t ht
    have hx' : x ∈ interior K₁ ∩ interior K₂ := by
      rw [interior_inter] at hx; exact hx
    rw [show ((ν₁ + ν₂ : ℕ) : ℝ) = (ν₁ : ℝ) + (ν₂ : ℝ) from by push_cast; ring,
        f.log_homog x hx'.1 t ht, g.log_homog x hx'.2 t ht]
    ring
  barrier := by
    intros x hx
    -- Case-split on whether `x ∈ interior K_i` for each `i`. The
    -- relevant filter is `nhdsWithin x (interior (K₁ ∩ K₂)) =
    -- nhdsWithin x (interior K₁ ∩ interior K₂)`.
    rw [interior_inter]
    have hx_cl : x ∈ closure (K₁ ∩ K₂) := frontier_subset_closure hx
    have hx_not_int : x ∉ interior K₁ ∩ interior K₂ := by
      rw [← interior_inter]; exact hx.2
    have hx_cl₁ : x ∈ closure K₁ :=
      closure_mono Set.inter_subset_left hx_cl
    have hx_cl₂ : x ∈ closure K₂ :=
      closure_mono Set.inter_subset_right hx_cl
    have h_inter_sub₁ : interior K₁ ∩ interior K₂ ⊆ interior K₁ :=
      Set.inter_subset_left
    have h_inter_sub₂ : interior K₁ ∩ interior K₂ ⊆ interior K₂ :=
      Set.inter_subset_right
    by_cases h₁ : x ∈ interior K₁
    · -- x ∈ interior K₁, so x ∉ interior K₂, hence x ∈ frontier K₂.
      have h₂ : x ∉ interior K₂ := fun hI₂ => hx_not_int ⟨h₁, hI₂⟩
      have hx_fr₂ : x ∈ frontier K₂ := ⟨hx_cl₂, h₂⟩
      have h_g : Filter.Tendsto g.f
          (nhdsWithin x (interior K₁ ∩ interior K₂)) Filter.atTop :=
        (g.barrier x hx_fr₂).mono_left (nhdsWithin_mono _ h_inter_sub₂)
      -- f.f is continuous at x (differentiable from contDiff).
      have h_f_cont : Filter.Tendsto f.f
          (nhdsWithin x (interior K₁ ∩ interior K₂)) (nhds (f.f x)) := by
        have h_diff : DifferentiableAt ℝ f.f x :=
          (f.contDiff₃.differentiableOn (by norm_num)).differentiableAt
            (isOpen_interior.mem_nhds h₁)
        exact h_diff.continuousAt.mono_left nhdsWithin_le_nhds
      -- g + f → atTop via Tendsto.atTop_add (atTop + finite = atTop).
      have h_sum : Filter.Tendsto (fun v => g.f v + f.f v)
          (nhdsWithin x (interior K₁ ∩ interior K₂)) Filter.atTop :=
        h_g.atTop_add h_f_cont
      exact h_sum.congr (fun _ => add_comm _ _)
    · -- x ∉ interior K₁, hence x ∈ frontier K₁.
      have hx_fr₁ : x ∈ frontier K₁ := ⟨hx_cl₁, h₁⟩
      have h_f : Filter.Tendsto f.f
          (nhdsWithin x (interior K₁ ∩ interior K₂)) Filter.atTop :=
        (f.barrier x hx_fr₁).mono_left (nhdsWithin_mono _ h_inter_sub₁)
      by_cases h₂ : x ∈ interior K₂
      · -- g.f continuous at x.
        have h_g_cont : Filter.Tendsto g.f
            (nhdsWithin x (interior K₁ ∩ interior K₂)) (nhds (g.f x)) := by
          have h_diff : DifferentiableAt ℝ g.f x :=
            (g.contDiff₃.differentiableOn (by norm_num)).differentiableAt
              (isOpen_interior.mem_nhds h₂)
          exact h_diff.continuousAt.mono_left nhdsWithin_le_nhds
        exact h_f.atTop_add h_g_cont
      · -- x ∈ frontier K₂.
        have hx_fr₂ : x ∈ frontier K₂ := ⟨hx_cl₂, h₂⟩
        have h_g : Filter.Tendsto g.f
            (nhdsWithin x (interior K₁ ∩ interior K₂)) Filter.atTop :=
          (g.barrier x hx_fr₂).mono_left (nhdsWithin_mono _ h_inter_sub₂)
        -- f + g ≥ f (eventually g ≥ 0 from atTop); use monotonicity.
        have h_g_nn : ∀ᶠ v in nhdsWithin x (interior K₁ ∩ interior K₂),
            (0 : ℝ) ≤ g.f v := h_g.eventually (Filter.eventually_ge_atTop 0)
        refine Filter.tendsto_atTop_mono' _ ?_ h_f
        filter_upwards [h_g_nn] with v hv using by linarith

/-- **Derived gradient of a sum.** `(f.add g).grad x = f.grad x +
g.grad x` on `int(K₁ ∩ K₂)`. Follows from `fderiv_fun_add` (Mathlib)
applied to the differentiable functions `f.f` and `g.f` (each
differentiable on its respective interior, from `contDiff`), plus
additivity of `toDual.symm`. -/
theorem add_grad {K₁ K₂ : Set V} {ν₁ ν₂ : ℕ} {d₁ d₂ : ℕ∞}
    (f : LHSCB V K₁ ν₁ d₁) (g : LHSCB V K₂ ν₂ d₂)
    {u : V} (hu : u ∈ interior K₁ ∩ interior K₂) :
    (f.add g).grad u = f.grad u + g.grad u := by
  obtain ⟨hu₁, hu₂⟩ := hu
  have hdiff₁ : DifferentiableAt ℝ f.f u :=
    (f.contDiff₃.differentiableOn (by norm_num)).differentiableAt
      (isOpen_interior.mem_nhds hu₁)
  have hdiff₂ : DifferentiableAt ℝ g.f u :=
    (g.contDiff₃.differentiableOn (by norm_num)).differentiableAt
      (isOpen_interior.mem_nhds hu₂)
  show (InnerProductSpace.toDual ℝ V).symm
      (fderiv ℝ (fun v => f.f v + g.f v) u) = _
  rw [fderiv_fun_add hdiff₁ hdiff₂, map_add]
  rfl

/-- **Strict convexity** of an LHSCB on `int(K)`, captured by strict
gradient monotonicity: `⟨u - v, ∇f(u) - ∇f(v)⟩ > 0` whenever `u ≠ v`.
This is a *separate* predicate because lifted barriers (e.g. an
LHSCB on `Y` extended trivially to `X × Y × ℝ`) are NOT strictly
convex — they only depend on one block of coordinates. The user's
`fBarrier` on `K ⊆ Y` is expected to satisfy this on `int K`, but
its lift to `H` does not. -/
def IsStrict {K : Set V} {ν : ℕ} {d : ℕ∞} (f : LHSCB V K ν d) : Prop :=
  ∀ u ∈ interior K, ∀ v ∈ interior K, u ≠ v →
    0 < inner ℝ (u - v) (f.grad u - f.grad v)

/-- **Euler identity** (theorem). `⟨u, ∇f(u)⟩ = -ν` follows from
`log_homog` by differentiating `f(t · u) = f(u) - ν · log t` at
`t = 1`. -/
theorem euler {K : Set V} {ν : ℕ} {d : ℕ∞} (f : LHSCB V K ν d) :
    ∀ u ∈ interior K, inner ℝ u (f.grad u) = -(ν : ℝ) := by
  intro u hu
  -- `f.f` is differentiable at `u`.
  have h_diff_f : DifferentiableAt ℝ f.f u :=
    (f.contDiff₃.differentiableOn (by norm_num)).differentiableAt
      (isOpen_interior.mem_nhds hu)
  -- Chain rule: `g(t) := f.f(t • u)` has derivative `(fderiv f.f u) u` at t = 1.
  let L : ℝ →L[ℝ] V := (1 : ℝ →L[ℝ] ℝ).smulRight u
  have h_L_smul : HasFDerivAt (fun t : ℝ => t • u) L 1 := L.hasFDerivAt
  have h_f_at_u : HasFDerivAt f.f (fderiv ℝ f.f u) ((1 : ℝ) • u) := by
    rw [one_smul]; exact h_diff_f.hasFDerivAt
  have h_chain : HasDerivAt (fun t : ℝ => f.f (t • u))
      ((fderiv ℝ f.f u) u) 1 := by
    have h_comp : HasFDerivAt (fun t : ℝ => f.f (t • u))
        ((fderiv ℝ f.f u).comp L) 1 := h_f_at_u.comp 1 h_L_smul
    have := h_comp.hasDerivAt
    convert this using 1
    show (fderiv ℝ f.f u) u =
      ((fderiv ℝ f.f u).comp L) 1
    rw [ContinuousLinearMap.comp_apply]
    show (fderiv ℝ f.f u) u = (fderiv ℝ f.f u) (L 1)
    congr 1
    show u = ((1 : ℝ →L[ℝ] ℝ).smulRight u) 1
    rw [ContinuousLinearMap.smulRight_apply]
    simp
  -- Other direction: `h(t) := f.f u - ν log t` has derivative `-ν` at t = 1.
  have h_explicit : HasDerivAt (fun t : ℝ => f.f u - (ν : ℝ) * Real.log t)
      (-(ν : ℝ)) 1 := by
    have h_log : HasDerivAt Real.log (1 : ℝ)⁻¹ 1 :=
      Real.hasDerivAt_log one_ne_zero
    have h_neg_log : HasDerivAt (fun t : ℝ => -((ν : ℝ) * Real.log t))
        (-((ν : ℝ) * (1 : ℝ)⁻¹)) 1 := (h_log.const_mul (ν : ℝ)).neg
    have h_add : HasDerivAt (fun t : ℝ => f.f u + -((ν : ℝ) * Real.log t))
        (-((ν : ℝ) * (1 : ℝ)⁻¹)) 1 := h_neg_log.const_add (f.f u)
    have heq : (fun t : ℝ => f.f u + -((ν : ℝ) * Real.log t))
        = (fun t : ℝ => f.f u - (ν : ℝ) * Real.log t) := by
      funext t; ring
    have hsimp : -((ν : ℝ) * (1 : ℝ)⁻¹) = -(ν : ℝ) := by simp
    rw [heq, hsimp] at h_add
    exact h_add
  -- The two functions agree on a neighborhood of 1 (where t > 0) via log_homog.
  have h_g_deriv : HasDerivAt (fun t : ℝ => f.f (t • u)) (-(ν : ℝ)) 1 := by
    apply h_explicit.congr_of_eventuallyEq
    have h_nhds : Set.Ioi (0 : ℝ) ∈ nhds (1 : ℝ) :=
      Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)
    filter_upwards [h_nhds] with t ht
    exact f.log_homog u hu t ht
  -- Uniqueness of HasDerivAt gives `(fderiv f.f u) u = -ν`.
  have h_eq : (fderiv ℝ f.f u) u = -(ν : ℝ) := h_chain.unique h_g_deriv
  -- Riesz: `⟨f.grad u, u⟩ = (fderiv f.f u) u`.
  have h_riesz : inner ℝ (f.grad u) u = (fderiv ℝ f.f u) u := by
    show inner ℝ ((InnerProductSpace.toDual ℝ V).symm (fderiv ℝ f.f u)) u = _
    rw [InnerProductSpace.toDual_symm_apply]
  rw [real_inner_comm, h_riesz, h_eq]

/-- **Hessian-times-self identity** (bilinear form). On `int K`,
`(fderiv ℝ (fderiv ℝ f.f) x) x = -fderiv ℝ f.f x` (CLM equality).
Differentiates the Euler-as-fderiv identity `(fderiv f.f y) y = -ν`
and uses Hessian symmetry. -/
theorem hessian_fderiv_apply_self {K : Set V} {ν : ℕ} {d : ℕ∞}
    (f : LHSCB V K ν d) :
    ∀ x ∈ interior K, (fderiv ℝ (fderiv ℝ f.f) x) x = -fderiv ℝ f.f x := by
  intro x hx
  -- f.f is C³ on interior K (open).
  have hf_C3 : ContDiffOn ℝ 3 f.f (interior K) := f.contDiff₃
  have h_ff_diff_eventually : ∀ᶠ y in nhds x, HasFDerivAt f.f (fderiv ℝ f.f y) y := by
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    exact ((hf_C3.differentiableOn (by norm_num)).differentiableAt
      (isOpen_interior.mem_nhds hy)).hasFDerivAt
  have h_fderiv_C2 : ContDiffOn ℝ 2 (fderiv ℝ f.f) (interior K) := by
    have h1 : ContDiffOn ℝ 2 (fderivWithin ℝ f.f (interior K)) (interior K) := by
      have := hf_C3.fderivWithin isOpen_interior.uniqueDiffOn (m := 2) (by norm_num)
      simpa using this
    exact h1.congr (fun y hy => (fderivWithin_of_isOpen isOpen_interior hy).symm)
  have h_fderiv_diffAt_x : DifferentiableAt ℝ (fderiv ℝ f.f) x :=
    (h_fderiv_C2.differentiableOn (by norm_num)).differentiableAt
      (isOpen_interior.mem_nhds hx)
  -- Hessian symmetry.
  have h_sym : ∀ v w : V,
      (fderiv ℝ (fderiv ℝ f.f) x) v w = (fderiv ℝ (fderiv ℝ f.f) x) w v :=
    second_derivative_symmetric_of_eventually h_ff_diff_eventually
      h_fderiv_diffAt_x.hasFDerivAt
  -- e(y) := (fderiv f.f y) y has HasFDerivAt at x via `clm_apply` chain rule.
  have h_e_HasFDerivAt : HasFDerivAt (fun y => (fderiv ℝ f.f y) y)
      ((fderiv ℝ f.f x).comp (ContinuousLinearMap.id ℝ V) +
       (fderiv ℝ (fderiv ℝ f.f) x).flip x) x :=
    h_fderiv_diffAt_x.hasFDerivAt.clm_apply (hasFDerivAt_id x)
  -- e is eventually -ν (via Euler + Riesz: ⟨y, ∇f y⟩ = -ν, and ⟨y, ∇f y⟩ = (fderiv f.f y) y).
  have h_e_const : (fun y => (fderiv ℝ f.f y) y) =ᶠ[nhds x] (fun _ => -(ν : ℝ)) := by
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    have h1 : (fderiv ℝ f.f y) y = inner ℝ (f.grad y) y := by
      show (fderiv ℝ f.f y) y =
        inner ℝ ((InnerProductSpace.toDual ℝ V).symm (fderiv ℝ f.f y)) y
      rw [InnerProductSpace.toDual_symm_apply]
    rw [h1, real_inner_comm]
    exact f.euler y hy
  have h_const_at_x : HasFDerivAt (fun _ : V => -(ν : ℝ)) (0 : V →L[ℝ] ℝ) x :=
    hasFDerivAt_const _ _
  have h_e_zero : HasFDerivAt (fun y => (fderiv ℝ f.f y) y) 0 x :=
    h_const_at_x.congr_of_eventuallyEq h_e_const
  -- The two CLMs are equal.
  have h_clm_zero :
      (fderiv ℝ f.f x).comp (ContinuousLinearMap.id ℝ V) +
        (fderiv ℝ (fderiv ℝ f.f) x).flip x = 0 :=
    h_e_HasFDerivAt.unique h_e_zero
  -- Extract pointwise + apply Hessian symmetry.
  ext h
  have hh := ContinuousLinearMap.ext_iff.mp h_clm_zero h
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.zero_apply] at hh
  -- hh : (fderiv f.f x) h + (fderiv (fderiv f.f) x) h x = 0
  rw [h_sym h x] at hh
  -- hh : (fderiv f.f x) h + (fderiv (fderiv f.f) x) x h = 0
  show (fderiv ℝ (fderiv ℝ f.f) x) x h = -((fderiv ℝ f.f x) h)
  linarith

/-- **Inner-product form of the Hessian-times-self identity.**
For all `h ∈ V`, `(fderiv ℝ (fderiv ℝ f.f) x) x h = -inner ℝ h (f.grad x)`
on `int K`. This is the `‖∇f‖²_{(∇²f)⁻¹} = ν` setup translated to
inner products (the actual identity follows by setting `h = -y` and
applying Euler). -/
theorem hessian_fderiv_apply_self_inner {K : Set V} {ν : ℕ} {d : ℕ∞}
    (f : LHSCB V K ν d) :
    ∀ x ∈ interior K, ∀ h : V,
      (fderiv ℝ (fderiv ℝ f.f) x) x h = -inner ℝ h (f.grad x) := by
  intro x hx h
  rw [f.hessian_fderiv_apply_self x hx]
  show -((fderiv ℝ f.f x) h) = -inner ℝ h (f.grad x)
  have h_riesz : (fderiv ℝ f.f x) h = inner ℝ h (f.grad x) := by
    show (fderiv ℝ f.f x) h =
      inner ℝ h ((InnerProductSpace.toDual ℝ V).symm (fderiv ℝ f.f x))
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
  rw [h_riesz]

-- `self_concordant_hessian_nonneg` was moved before `LHSCB.add` so that the
-- sum's `self_concordant` proof can use it.

/-- **Gradient monotonicity** (theorem). Convexity of `interior K`
plus `D²f ≥ 0` (from `self_concordant`) imply that `t ↦ ⟨u-v, ∇f(v +
t(u-v))⟩` is monotone on `[0, 1]`, hence `⟨u-v, ∇f(u) - ∇f(v)⟩ ≥ 0`.

Proof strategy: define `ψ(t) := (fderiv f.f (v + t(u-v))) (u-v)`.
By chain rule, `ψ'(t) = (fderiv (fderiv f.f) (γ t)) (u-v) (u-v)`,
which by `iteratedFDerivWithin_two_apply` (on open `interior K`)
equals `iteratedFDerivWithin 2 f.f (interior K) (γ t) (fun _ => u-v)`,
nonneg by `self_concordant_hessian_nonneg`. Then
`monotoneOn_of_hasDerivWithinAt_nonneg` gives `ψ` monotone on `[0,1]`,
so `ψ(0) ≤ ψ(1)`. Riesz translates this to the inner-product form. -/
theorem grad_monotone {K : Set V} {ν : ℕ} {d : ℕ∞} (f : LHSCB V K ν d)
    (hK_conv : Convex ℝ (interior K)) :
    ∀ u ∈ interior K, ∀ v ∈ interior K,
      0 ≤ inner ℝ (u - v) (f.grad u - f.grad v) := by
  intros u hu v hv
  set w : V := u - v with hw_def
  set γ : ℝ → V := fun t => v + t • w with hγ_def
  -- γ has derivative w everywhere and γ(0) = v, γ(1) = u.
  have hγ_deriv : ∀ t : ℝ, HasDerivAt γ w t := fun t => by
    have h := (hasDerivAt_const t v).add ((hasDerivAt_id t).smul_const w)
    simpa using h
  have hγ_cont : Continuous γ :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hγ0 : γ 0 = v := by show v + (0:ℝ) • w = v; simp
  have hγ1 : γ 1 = u := by
    show v + (1:ℝ) • w = u
    simp [w]
  -- For t ∈ Icc 0 1, γ(t) ∈ interior K.
  have hγ_mem : ∀ t ∈ Set.Icc (0:ℝ) 1, γ t ∈ interior K := by
    intro t ⟨h0, h1⟩
    have heq : γ t = (1 - t) • v + t • u := by
      show v + t • (u - v) = (1 - t) • v + t • u
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [heq]
    exact hK_conv hv hu (by linarith) h0 (by linarith)
  -- f.f is C³ on interior K, so fderiv f.f is C² there, hence differentiable.
  have hf_C3 : ContDiffOn ℝ 3 f.f (interior K) := f.contDiff₃
  have h_fderiv_eqOn : Set.EqOn (fderivWithin ℝ f.f (interior K)) (fderiv ℝ f.f)
      (interior K) := fun y hy => fderivWithin_of_isOpen isOpen_interior hy
  have h_fderiv_C2 : ContDiffOn ℝ 2 (fderiv ℝ f.f) (interior K) := by
    have h1 : ContDiffOn ℝ 2 (fderivWithin ℝ f.f (interior K)) (interior K) := by
      have := hf_C3.fderivWithin isOpen_interior.uniqueDiffOn (m := 2) (by norm_num)
      simpa using this
    exact h1.congr (fun y hy => (fderivWithin_of_isOpen isOpen_interior hy).symm)
  have h_fderiv_diffAt : ∀ x ∈ interior K, DifferentiableAt ℝ (fderiv ℝ f.f) x :=
    fun x hx => (h_fderiv_C2.differentiableOn (by norm_num)).differentiableAt
      (isOpen_interior.mem_nhds hx)
  -- ψ(t) := (fderiv ℝ f.f (γ t)) w.
  set ψ : ℝ → ℝ := fun t => (fderiv ℝ f.f (γ t)) w with hψ_def
  -- ψ continuous on Icc 0 1: composition of continuous things on the open set.
  have hψ_cont : ContinuousOn ψ (Set.Icc 0 1) := by
    have h_fderiv_cont : ContinuousOn (fderiv ℝ f.f) (interior K) :=
      h_fderiv_C2.continuousOn
    have h_comp_cont : ContinuousOn (fderiv ℝ f.f ∘ γ) (Set.Icc 0 1) :=
      h_fderiv_cont.comp hγ_cont.continuousOn hγ_mem
    have h_eval : Continuous (fun L : V →L[ℝ] ℝ => L w) :=
      (ContinuousLinearMap.apply ℝ ℝ w).continuous
    exact h_eval.comp_continuousOn h_comp_cont
  -- For t ∈ Ioo 0 1, HasDerivAt ψ (Hessian quadratic form) t.
  have hψ_deriv : ∀ t ∈ Set.Ioo (0:ℝ) 1,
      HasDerivAt ψ ((fderiv ℝ (fderiv ℝ f.f) (γ t)) w w) t := by
    intro t ht
    have htmem : γ t ∈ interior K := hγ_mem t (Set.Ioo_subset_Icc_self ht)
    -- HasFDerivAt of `fderiv f.f` at γ(t).
    have h_fderiv_fderiv : HasFDerivAt (fderiv ℝ f.f)
        (fderiv ℝ (fderiv ℝ f.f) (γ t)) (γ t) :=
      (h_fderiv_diffAt (γ t) htmem).hasFDerivAt
    -- HasDerivAt of (fderiv f.f ∘ γ) at t: chain rule.
    have h_comp : HasDerivAt (fun s : ℝ => fderiv ℝ f.f (γ s))
        ((fderiv ℝ (fderiv ℝ f.f) (γ t)) w) t :=
      h_fderiv_fderiv.comp_hasDerivAt t (hγ_deriv t)
    -- Apply CLM `eval w` to convert to HasDerivAt for ψ.
    have h_eval_clm : HasFDerivAt (fun L : V →L[ℝ] ℝ => L w)
        (ContinuousLinearMap.apply ℝ ℝ w) (fderiv ℝ f.f (γ t)) :=
      (ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt
    have := h_eval_clm.comp_hasDerivAt t h_comp
    simpa [ψ] using this
  -- The Hessian quadratic form is ≥ 0 (via the iteratedFDerivWithin identification).
  have hψ_deriv_nonneg : ∀ t ∈ Set.Ioo (0:ℝ) 1,
      0 ≤ (fderiv ℝ (fderiv ℝ f.f) (γ t)) w w := by
    intro t ht
    have htmem : γ t ∈ interior K := hγ_mem t (Set.Ioo_subset_Icc_self ht)
    have h_hess_nn := f.self_concordant_hessian_nonneg (γ t) htmem w
    -- Identify: iteratedFDerivWithin 2 f.f (interior K) (γ t) [w, w]
    --         = iteratedFDeriv 2 f.f (γ t) [w, w]    (open set)
    --         = (fderiv (fderiv f.f) (γ t)) w w     (iteratedFDeriv_two_apply)
    have h_eq1 : iteratedFDerivWithin ℝ 2 f.f (interior K) (γ t) (fun _ => w) =
        iteratedFDeriv ℝ 2 f.f (γ t) (fun _ => w) := by
      congr 1
      exact iteratedFDerivWithin_of_isOpen 2 isOpen_interior htmem
    have h_eq2 : iteratedFDeriv ℝ 2 f.f (γ t) (fun _ => w) =
        (fderiv ℝ (fderiv ℝ f.f) (γ t)) w w := by
      rw [iteratedFDeriv_two_apply]
    rw [← h_eq2, ← h_eq1]
    exact h_hess_nn
  -- Apply monotoneOn_of_hasDerivWithinAt_nonneg.
  have hψ_mono : MonotoneOn ψ (Set.Icc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1) hψ_cont
    · intro t ht
      rw [interior_Icc] at ht
      exact (hψ_deriv t ht).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact hψ_deriv_nonneg t ht
  -- ψ(0) ≤ ψ(1).
  have h_psi_le : ψ 0 ≤ ψ 1 :=
    hψ_mono ⟨le_refl _, by norm_num⟩ ⟨by norm_num, le_refl _⟩ (by norm_num)
  -- Translate via Riesz: ψ(t) = ⟨f.grad (γ t), w⟩.
  have h_riesz : ∀ x : V, (fderiv ℝ f.f x) w = inner ℝ (f.grad x) w := by
    intro x
    show (fderiv ℝ f.f x) w =
      inner ℝ ((InnerProductSpace.toDual ℝ V).symm (fderiv ℝ f.f x)) w
    rw [InnerProductSpace.toDual_symm_apply]
  have h_psi_0 : ψ 0 = inner ℝ (f.grad v) w := by
    show (fderiv ℝ f.f (γ 0)) w = _; rw [hγ0]; exact h_riesz v
  have h_psi_1 : ψ 1 = inner ℝ (f.grad u) w := by
    show (fderiv ℝ f.f (γ 1)) w = _; rw [hγ1]; exact h_riesz u
  rw [h_psi_0, h_psi_1] at h_psi_le
  rw [real_inner_comm w (f.grad u), real_inner_comm w (f.grad v)] at h_psi_le
  rw [inner_sub_right]
  linarith

/-- **LHSCB gradient inequality** (convexity in gradient form). For
`u, v ∈ int K`, `f(v) ≥ f(u) + ⟨∇f(u), v - u⟩`.

Proof: define `γ(t) = u + t(v - u)` (so `γ 0 = u`, `γ 1 = v`) and
`φ(t) := f.f(γ t) - f.f u - t · ⟨∇f u, v-u⟩`. Then `φ(0) = 0`, and
`φ'(t) = ⟨∇f(γ t) - ∇f u, v-u⟩ ≥ 0` (for `t > 0`, by `grad_monotone`
applied to `γ(t)` and `u`, dividing out the `t` factor). Hence `φ`
monotone on `[0, 1]`, so `φ(1) ≥ φ(0) = 0`. -/
theorem grad_inequality {K : Set V} {ν : ℕ} {d : ℕ∞} (f : LHSCB V K ν d)
    (hK_conv : Convex ℝ (interior K)) :
    ∀ u ∈ interior K, ∀ v ∈ interior K,
      f.f v ≥ f.f u + inner ℝ (f.grad u) (v - u) := by
  intros u hu v hv
  set w : V := v - u with hw_def
  set γ : ℝ → V := fun t => u + t • w with hγ_def
  have hγ_deriv : ∀ t : ℝ, HasDerivAt γ w t := fun t => by
    have h := (hasDerivAt_const t u).add ((hasDerivAt_id t).smul_const w)
    simpa using h
  have hγ_cont : Continuous γ :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hγ0 : γ 0 = u := by show u + (0:ℝ) • w = u; simp
  have hγ1 : γ 1 = v := by show u + (1:ℝ) • w = v; simp [w]
  have hγ_mem : ∀ t ∈ Set.Icc (0:ℝ) 1, γ t ∈ interior K := by
    intro t ⟨h0, h1⟩
    have heq : γ t = (1 - t) • u + t • v := by
      show u + t • (v - u) = (1 - t) • u + t • v
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [heq]
    exact hK_conv hu hv (by linarith) h0 (by linarith)
  have hf_diffOn : DifferentiableOn ℝ f.f (interior K) :=
    f.contDiff₃.differentiableOn (by norm_num)
  set c : ℝ := inner ℝ (f.grad u) w with hc_def
  set φ : ℝ → ℝ := fun t => f.f (γ t) - f.f u - t * c with hφ_def
  -- φ continuous on Icc 0 1.
  have hφ_cont : ContinuousOn φ (Set.Icc 0 1) := by
    have h_comp : ContinuousOn (fun t => f.f (γ t)) (Set.Icc 0 1) :=
      hf_diffOn.continuousOn.comp hγ_cont.continuousOn hγ_mem
    apply ContinuousOn.sub
    apply ContinuousOn.sub h_comp continuousOn_const
    exact (continuous_id.mul continuous_const).continuousOn
  -- HasDerivAt of φ at each t ∈ Ioo 0 1.
  have hφ_deriv : ∀ t ∈ Set.Ioo (0:ℝ) 1,
      HasDerivAt φ (inner ℝ (f.grad (γ t)) w - c) t := by
    intro t ht
    have htmem : γ t ∈ interior K := hγ_mem t (Set.Ioo_subset_Icc_self ht)
    have hf_diff_at : DifferentiableAt ℝ f.f (γ t) :=
      hf_diffOn.differentiableAt (isOpen_interior.mem_nhds htmem)
    have h_fderiv : HasFDerivAt f.f (fderiv ℝ f.f (γ t)) (γ t) :=
      hf_diff_at.hasFDerivAt
    have h_comp_fc : HasDerivAt (fun s : ℝ => f.f (γ s))
        ((fderiv ℝ f.f (γ t)) w) t :=
      h_fderiv.comp_hasDerivAt t (hγ_deriv t)
    -- Riesz: (fderiv f.f (γ t)) w = ⟨f.grad (γ t), w⟩.
    have h_riesz : (fderiv ℝ f.f (γ t)) w = inner ℝ (f.grad (γ t)) w := by
      show (fderiv ℝ f.f (γ t)) w =
        inner ℝ ((InnerProductSpace.toDual ℝ V).symm (fderiv ℝ f.f (γ t))) w
      rw [InnerProductSpace.toDual_symm_apply]
    rw [h_riesz] at h_comp_fc
    have h_const : HasDerivAt (fun _ : ℝ => f.f u) (0 : ℝ) t :=
      hasDerivAt_const t (f.f u)
    have h_linear : HasDerivAt (fun s : ℝ => s * c) c t := by
      have := (hasDerivAt_id t).mul_const c
      simpa using this
    have := (h_comp_fc.sub h_const).sub h_linear
    convert this using 1
    ring
  -- φ' ≥ 0 on Ioo 0 1 (from grad_monotone applied at γ(t) and u).
  have hφ_deriv_nonneg : ∀ t ∈ Set.Ioo (0:ℝ) 1,
      0 ≤ inner ℝ (f.grad (γ t)) w - c := by
    intro t ht
    have htmem : γ t ∈ interior K := hγ_mem t (Set.Ioo_subset_Icc_self ht)
    have ht_pos : 0 < t := ht.1
    have h_mono := f.grad_monotone hK_conv (γ t) htmem u hu
    have h_diff_eq : γ t - u = t • w := by show u + t • w - u = t • w; abel
    rw [h_diff_eq, inner_smul_left, conj_trivial] at h_mono
    -- h_mono : 0 ≤ t * inner ℝ w (f.grad (γ t) - f.grad u)
    have h_inner_nn : 0 ≤ inner ℝ w (f.grad (γ t) - f.grad u) :=
      (mul_nonneg_iff_of_pos_left ht_pos).mp h_mono
    rw [inner_sub_right] at h_inner_nn
    show 0 ≤ inner ℝ (f.grad (γ t)) w - c
    rw [hc_def]
    have h_swap1 : inner ℝ w (f.grad (γ t)) = inner ℝ (f.grad (γ t)) w :=
      real_inner_comm _ _
    have h_swap2 : inner ℝ w (f.grad u) = inner ℝ (f.grad u) w :=
      real_inner_comm _ _
    rw [h_swap1, h_swap2] at h_inner_nn
    linarith
  -- φ monotone on Icc 0 1.
  have hφ_mono : MonotoneOn φ (Set.Icc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1) hφ_cont
    · intro t ht
      rw [interior_Icc] at ht
      exact (hφ_deriv t ht).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact hφ_deriv_nonneg t ht
  have h_le : φ 0 ≤ φ 1 :=
    hφ_mono ⟨le_refl _, by norm_num⟩ ⟨by norm_num, le_refl _⟩ (by norm_num)
  have hφ0 : φ 0 = 0 := by show f.f (γ 0) - f.f u - 0 * c = 0; rw [hγ0]; ring
  have hφ1 : φ 1 = f.f v - f.f u - c := by
    show f.f (γ 1) - f.f u - 1 * c = _; rw [hγ1]; ring
  rw [hφ0, hφ1] at h_le
  show f.f u + c ≤ f.f v
  linarith

/-- **LHSCB gradient blow-up at the boundary** (Euclidean norm).
As `u → x` within `int K` for `x ∈ frontier K`, `‖∇f(u)‖ → ∞`.

Proof: fix `u₀ ∈ interior K`. By `grad_inequality` at `u`:
`f(u₀) ≥ f(u) + ⟨∇f(u), u₀ - u⟩`, hence `⟨∇f(u), u - u₀⟩ ≥ f(u) - f(u₀)`.
By Cauchy-Schwarz: `‖∇f(u)‖ · ‖u - u₀‖ ≥ f(u) - f(u₀)`.
For u near x, `‖u - u₀‖ ≤ 2‖x - u₀‖`, so
`‖∇f(u)‖ ≥ (f(u) - f(u₀)) / (2‖x - u₀‖) → ∞` as `f(u) → ∞`. -/
theorem grad_norm_tendsto_atTop {K : Set V} {ν : ℕ} {d : ℕ∞}
    (f : LHSCB V K ν d)
    (hK_conv : Convex ℝ (interior K))
    (hK_int_nonempty : (interior K).Nonempty) :
    ∀ x ∈ frontier K,
      Filter.Tendsto (fun u => ‖f.grad u‖) (nhdsWithin x (interior K))
        Filter.atTop := by
  intro x hx
  obtain ⟨u₀, hu₀⟩ := hK_int_nonempty
  -- x ≠ u₀ since x ∈ frontier K and u₀ ∈ interior K (disjoint by definition of frontier).
  have h_xne : x ≠ u₀ := by
    intro h_eq
    have : u₀ ∉ interior K := h_eq ▸ hx.2
    exact this hu₀
  have h_xu0_pos : 0 < ‖x - u₀‖ := norm_sub_pos_iff.mpr h_xne
  -- f.f → ∞ on nhdsWithin.
  have h_barrier : Filter.Tendsto f.f (nhdsWithin x (interior K)) Filter.atTop :=
    f.barrier x hx
  -- Constant: 2 ‖x - u₀‖ > 0.
  set C : ℝ := 2 * ‖x - u₀‖ with hC_def
  have hC_pos : 0 < C := by positivity
  -- Eventually ‖u - u₀‖ ≤ C.
  have h_tendsto_norm : Filter.Tendsto (fun u => ‖u - u₀‖)
      (nhdsWithin x (interior K)) (nhds ‖x - u₀‖) :=
    ((continuous_id.sub continuous_const).norm).continuousAt.mono_left
      nhdsWithin_le_nhds
  have h_norm_eventually : ∀ᶠ u in nhdsWithin x (interior K), ‖u - u₀‖ ≤ C := by
    have : ∀ᶠ u in nhdsWithin x (interior K), ‖u - u₀‖ < ‖x - u₀‖ + ‖x - u₀‖ :=
      h_tendsto_norm (Iio_mem_nhds (by linarith))
    filter_upwards [this] with u hu
    show ‖u - u₀‖ ≤ 2 * ‖x - u₀‖
    linarith
  -- (f.f u - f.f u₀) / C → ∞ as f.f u → ∞.
  have h_shifted : Filter.Tendsto (fun u => f.f u - f.f u₀)
      (nhdsWithin x (interior K)) Filter.atTop := by
    have h_neg : Filter.Tendsto (fun _ : V => -f.f u₀)
        (nhdsWithin x (interior K)) (nhds (-f.f u₀)) := tendsto_const_nhds
    have := h_barrier.atTop_add h_neg
    refine this.congr fun u => ?_
    show f.f u + -f.f u₀ = f.f u - f.f u₀
    ring
  have h_quot : Filter.Tendsto (fun u => (f.f u - f.f u₀) / C)
      (nhdsWithin x (interior K)) Filter.atTop :=
    h_shifted.atTop_div_const hC_pos
  -- For u with u ∈ interior K and ‖u - u₀‖ ≤ C, ‖∇f u‖ ≥ (f.f u - f.f u₀) / C.
  have h_bound_eventually : ∀ᶠ u in nhdsWithin x (interior K),
      (f.f u - f.f u₀) / C ≤ ‖f.grad u‖ := by
    have h_self : ∀ᶠ u in nhdsWithin x (interior K), u ∈ interior K :=
      self_mem_nhdsWithin
    filter_upwards [h_norm_eventually, h_self] with u h_norm_le h_u_int
    -- grad_inequality at u: f.f u₀ ≥ f.f u + ⟨∇f u, u₀ - u⟩
    have h_ineq := f.grad_inequality hK_conv u h_u_int u₀ hu₀
    -- ⟨∇f u, u - u₀⟩ = -⟨∇f u, u₀ - u⟩
    have h_neg : inner ℝ (f.grad u) (u₀ - u) = -inner ℝ (f.grad u) (u - u₀) := by
      rw [← inner_neg_right, neg_sub]
    -- ⟨∇f u, u - u₀⟩ ≥ f.f u - f.f u₀
    have h_lower : f.f u - f.f u₀ ≤ inner ℝ (f.grad u) (u - u₀) := by
      have h_combined : f.f u - inner ℝ (f.grad u) (u - u₀) ≤ f.f u₀ := by
        have := h_ineq
        rw [h_neg] at this
        linarith
      linarith
    -- CS: ⟨∇f u, u - u₀⟩ ≤ ‖∇f u‖ ‖u - u₀‖
    have h_cs : inner ℝ (f.grad u) (u - u₀) ≤ ‖f.grad u‖ * ‖u - u₀‖ :=
      real_inner_le_norm _ _
    -- So f.f u - f.f u₀ ≤ ‖∇f u‖ * ‖u - u₀‖ ≤ ‖∇f u‖ * C
    -- (For non-negative f.f u - f.f u₀; otherwise the bound trivially holds.)
    by_cases h_pos : 0 ≤ f.f u - f.f u₀
    · have h_norm_grad_nn : 0 ≤ ‖f.grad u‖ := norm_nonneg _
      have h_prod_bound : ‖f.grad u‖ * ‖u - u₀‖ ≤ ‖f.grad u‖ * C :=
        mul_le_mul_of_nonneg_left h_norm_le h_norm_grad_nn
      have h_total : f.f u - f.f u₀ ≤ ‖f.grad u‖ * C := by linarith
      exact (div_le_iff₀ hC_pos).mpr h_total
    · replace h_pos : f.f u - f.f u₀ < 0 := not_le.mp h_pos
      have : (f.f u - f.f u₀) / C ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg h_pos.le hC_pos.le
      linarith [norm_nonneg (f.grad u)]
  -- Combine: (f.f u - f.f u₀)/C → ∞ and ‖∇f u‖ ≥ that, hence ‖∇f u‖ → ∞.
  exact Filter.tendsto_atTop_mono' _ h_bound_eventually h_quot

end LHSCB

end Irn
