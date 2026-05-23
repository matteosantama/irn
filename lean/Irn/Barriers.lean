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
