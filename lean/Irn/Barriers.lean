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

/-- **Gradient monotonicity** (theorem). Follows from
`self_concordant` via positivity of `D²f` (forced by the squared SC
bound: the cube of a negative would violate the nonnegativity of the
LHS square) and the mean value theorem applied to
`t ↦ ⟨u - v, ∇f((1-t) v + t u)⟩`.

Currently sorried. -/
theorem grad_monotone {K : Set V} {ν : ℕ} (f : LHSCB V K ν) :
    ∀ u ∈ interior K, ∀ v ∈ interior K,
      0 ≤ inner ℝ (u - v) (f.grad u - f.grad v) := by
  -- Convexity of `interior K` is needed for the MVT argument. The
  -- sorried proof should establish it from convexity of `K` (which
  -- in our use case follows from `K` being a convex cone).
  intro u _hu v _hv
  sorry

end LHSCB

end Irn
