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
* `euler` — `⟨u, ∇f(u)⟩ = -ν` (theorem from `log_homog`, currently
  sorried);
* `grad_monotone` — convexity in gradient form (theorem from
  `self_concordant`, currently sorried).

Other API:

* `LHSCB.add` — sum of a `ν₁`-LHSCB on `K₁` and a `ν₂`-LHSCB on `K₂`
  is a `(ν₁+ν₂)`-LHSCB on `K₁ ∩ K₂`. Uses `interior_inter`.
* `LHSCB.add_grad` — derived gradient of the sum equals the sum of
  derived gradients (via `fderiv.add` + Riesz linearity).
* `LHSCB.IsStrict` — separate predicate for strict convexity on
  `int(K)` (lifted barriers do not satisfy this).

Paper references:
* Definition 2 (`ν`-LHSCB)
* Eq. (2.2) (Euler identity)
* §2.1 (conjugate barriers)
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace Irn

open scoped InnerProductSpace

/-- An abstract `ν`-LHSCB on a real inner product space `V` with
respect to the (convex) cone `K ⊆ V`.

The gradient is *not* a field — see `LHSCB.grad`. -/
structure LHSCB (V : Type*)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (K : Set V) (ν : ℕ) where
  /-- The barrier function. -/
  f : V → ℝ
  /-- `f` is `C³` on `int(K)`. -/
  contDiff : ContDiffOn ℝ 3 f (interior K)
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
noncomputable def grad {K : Set V} {ν : ℕ} (f : LHSCB V K ν) : V → V :=
  fun x => (InnerProductSpace.toDual ℝ V).symm (fderiv ℝ f.f x)

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

/-- **Sum of LHSCBs.** A `ν₁`-LHSCB on `K₁` plus a `ν₂`-LHSCB on `K₂`
is a `(ν₁+ν₂)`-LHSCB on `K₁ ∩ K₂`. -/
noncomputable def add {K₁ K₂ : Set V} {ν₁ ν₂ : ℕ}
    (f : LHSCB V K₁ ν₁) (g : LHSCB V K₂ ν₂) :
    LHSCB V (K₁ ∩ K₂) (ν₁ + ν₂) where
  f := fun v => f.f v + g.f v
  contDiff := by
    rw [interior_inter]
    exact ContDiffOn.add
      (ContDiffOn.mono f.contDiff Set.inter_subset_left)
      (ContDiffOn.mono g.contDiff Set.inter_subset_right)
  self_concordant := by
    -- Nesterov's self-concordant sum theorem: the SC bound is closed
    -- under addition of barriers on a common interior. Requires
    -- expanding the cubed-and-squared form and using AM-GM-like
    -- inequalities on the Hessian/third-derivative pairings.
    -- Deferred.
    intro x _hx h
    sorry
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
          (f.contDiff.differentiableOn (by norm_num)).differentiableAt
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
            (g.contDiff.differentiableOn (by norm_num)).differentiableAt
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
theorem add_grad {K₁ K₂ : Set V} {ν₁ ν₂ : ℕ}
    (f : LHSCB V K₁ ν₁) (g : LHSCB V K₂ ν₂)
    {u : V} (hu : u ∈ interior K₁ ∩ interior K₂) :
    (f.add g).grad u = f.grad u + g.grad u := by
  obtain ⟨hu₁, hu₂⟩ := hu
  have hdiff₁ : DifferentiableAt ℝ f.f u :=
    (f.contDiff.differentiableOn (by norm_num)).differentiableAt
      (isOpen_interior.mem_nhds hu₁)
  have hdiff₂ : DifferentiableAt ℝ g.f u :=
    (g.contDiff.differentiableOn (by norm_num)).differentiableAt
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
def IsStrict {K : Set V} {ν : ℕ} (f : LHSCB V K ν) : Prop :=
  ∀ u ∈ interior K, ∀ v ∈ interior K, u ≠ v →
    0 < inner ℝ (u - v) (f.grad u - f.grad v)

/-- **Euler identity** (theorem). `⟨u, ∇f(u)⟩ = -ν` follows from
`log_homog` by differentiating `f(t · u) = f(u) - ν · log t` at
`t = 1`. -/
theorem euler {K : Set V} {ν : ℕ} (f : LHSCB V K ν) :
    ∀ u ∈ interior K, inner ℝ u (f.grad u) = -(ν : ℝ) := by
  intro u hu
  -- `f.f` is differentiable at `u`.
  have h_diff_f : DifferentiableAt ℝ f.f u :=
    (f.contDiff.differentiableOn (by norm_num)).differentiableAt
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

/-- **Hessian non-negativity from SC bound.** The squared SC bound
forces `D²f(x)[h,h] ≥ 0` (the cube of a negative is negative, but
the LHS is a square). -/
lemma self_concordant_hessian_nonneg {K : Set V} {ν : ℕ} (f : LHSCB V K ν) :
    ∀ x ∈ interior K, ∀ h : V,
      0 ≤ iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => h) := by
  intro x hx h
  by_contra hneg
  push_neg at hneg
  have hsc := f.self_concordant x hx h
  have h_cube : (iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => h)) ^ 3 < 0 :=
    Odd.pow_neg (by decide : Odd 3) hneg
  have h_sq : 0 ≤ (iteratedFDerivWithin ℝ 3 f.f (interior K) x (fun _ => h)) ^ 2 :=
    sq_nonneg _
  linarith

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
theorem grad_monotone {K : Set V} {ν : ℕ} (f : LHSCB V K ν)
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
  have hf_C3 : ContDiffOn ℝ 3 f.f (interior K) := f.contDiff
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

end LHSCB

end Irn
