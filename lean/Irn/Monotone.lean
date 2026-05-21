/-
# Monotone operator theory
Predicates and basic API for monotone (and strictly monotone) operators
on Hilbert spaces, plus a specialized Minty-style existence theorem
for continuous strictly monotone coercive operators on open convex
domains in finite-dimensional Hilbert spaces.
-/
import Mathlib
namespace Irn
open scoped InnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
/-! ## Monotonicity predicates -/
/-- `T : V → V` is **monotone on `s`** if
`⟨u - v, T u - T v⟩ ≥ 0` for all `u, v ∈ s`. -/
def IsMonotoneOn (T : V → V) (s : Set V) : Prop :=
  ∀ u ∈ s, ∀ v ∈ s, 0 ≤ inner ℝ (u - v) (T u - T v)
/-- `T : V → V` is **strictly monotone on `s`** if the inequality is
strict whenever `u ≠ v`. -/
def IsStrictMonotoneOn (T : V → V) (s : Set V) : Prop :=
  ∀ u ∈ s, ∀ v ∈ s, u ≠ v → 0 < inner ℝ (u - v) (T u - T v)
/-- Strict monotonicity implies monotonicity (the strict version uses
`u ≠ v`; for `u = v` both sides are 0). -/
theorem IsStrictMonotoneOn.isMonotoneOn {T : V → V} {s : Set V}
    (h : IsStrictMonotoneOn T s) : IsMonotoneOn T s := by
  intro u hu v hv
  by_cases huv : u = v
  · rw [huv, sub_self, inner_zero_left]
  · exact (h u hu v hv huv).le
/-- The sum of two monotone operators on the same set is monotone. -/
theorem IsMonotoneOn.add {T₁ T₂ : V → V} {s : Set V}
    (h₁ : IsMonotoneOn T₁ s) (h₂ : IsMonotoneOn T₂ s) :
    IsMonotoneOn (fun u => T₁ u + T₂ u) s := by
  intro u hu v hv
  have h1 := h₁ u hu v hv
  have h2 := h₂ u hu v hv
  have h_sub : (T₁ u + T₂ u) - (T₁ v + T₂ v) = (T₁ u - T₁ v) + (T₂ u - T₂ v) := by
    abel
  rw [h_sub, inner_add_right]
  linarith
/-- The sum of a monotone operator and a strictly monotone operator is
strictly monotone. -/
theorem IsMonotoneOn.add_strictMonotone {T₁ T₂ : V → V} {s : Set V}
    (h₁ : IsMonotoneOn T₁ s) (h₂ : IsStrictMonotoneOn T₂ s) :
    IsStrictMonotoneOn (fun u => T₁ u + T₂ u) s := by
  intro u hu v hv huv
  have h1 := h₁ u hu v hv
  have h2 := h₂ u hu v hv huv
  have h_sub : (T₁ u + T₂ u) - (T₁ v + T₂ v) = (T₁ u - T₁ v) + (T₂ u - T₂ v) := by
    abel
  rw [h_sub, inner_add_right]
  linarith
/-- Identity scaled by `μ > 0` is strictly monotone everywhere. -/
theorem IsStrictMonotoneOn.smul_id (s : Set V) {μ : ℝ} (hμ : 0 < μ) :
    IsStrictMonotoneOn (fun u : V => μ • u) s := by
  intro u _hu v _hv huv
  have h_sub : μ • u - μ • v = μ • (u - v) := by rw [smul_sub]
  rw [h_sub, inner_smul_right, real_inner_self_eq_norm_sq]
  have h_norm_pos : 0 < ‖u - v‖ ^ 2 := by
    have : 0 < ‖u - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr huv)
    positivity
  positivity
/-! ## Strong monotonicity -/
/-- `T : V → V` is **strongly monotone on `s`** with constant `α`
if `⟨u - v, T u - T v⟩ ≥ α ‖u - v‖²` for all `u, v ∈ s`. -/
def IsStronglyMonotoneOn (T : V → V) (s : Set V) (α : ℝ) : Prop :=
  ∀ u ∈ s, ∀ v ∈ s, α * ‖u - v‖ ^ 2 ≤ inner ℝ (u - v) (T u - T v)
/-- Strong monotonicity with `α > 0` implies strict monotonicity. -/
theorem IsStronglyMonotoneOn.isStrictMonotoneOn {T : V → V} {s : Set V}
    {α : ℝ} (hα : 0 < α) (h : IsStronglyMonotoneOn T s α) :
    IsStrictMonotoneOn T s := by
  intro u hu v hv huv
  have h1 := h u hu v hv
  have hpos : 0 < α * ‖u - v‖ ^ 2 := by
    apply mul_pos hα
    exact pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr huv)) 2
  linarith
/-
Strong monotonicity gives a bi-Lipschitz lower bound:
`α ‖u - v‖ ≤ ‖T u - T v‖`.
-/
theorem IsStronglyMonotoneOn.norm_sub_le {T : V → V} {s : Set V}
    {α : ℝ} (hα : 0 < α) (h : IsStronglyMonotoneOn T s α)
    {u v : V} (hu : u ∈ s) (hv : v ∈ s) :
    α * ‖u - v‖ ≤ ‖T u - T v‖ := by
  have := h u hu v hv;
  nlinarith [ norm_nonneg ( u - v ), norm_nonneg ( T u - T v ), abs_le.mp ( abs_real_inner_le_norm ( u - v ) ( T u - T v ) ) ]
/-! ## Corrected Minty-style existence theorem
The original theorem statement (with only strict monotonicity and boundary
coercivity) is **false** when `frontier s = ∅`, e.g. `s = V`. Counterexample:
`V = ℝ`, `T u = Real.exp u`, which is strictly monotone, continuous,
with `frontier ℝ = ∅` making the coercivity condition vacuous, yet
`exp u > 0` for all `u`, so `T` has no zero.
The corrected version below adds:
* **Strong monotonicity** (quantitative lower bound `α ‖u-v‖² ≤ ⟨u-v, Tu-Tv⟩`),
  which gives injectivity and properness (bi-Lipschitz from below).
* **C¹ regularity** (`ContDiffOn ℝ 1 T s`), which together with strong
  monotonicity gives that `DT(u)` is invertible at each point, allowing
  the inverse function theorem to establish openness of the image `T(s)`.
The proof then follows the classical argument:
1. `T(s)` is open (inverse function theorem).
2. `T(s)` is closed (strong monotonicity ⇒ Cauchy + boundary coercivity).
3. `V` is connected and `T(s)` is nonempty clopen, so `T(s) = V`.
4. In particular `0 ∈ T(s)`, giving existence; strong monotonicity gives
   uniqueness. -/
/-
Strong monotonicity of `T` on an open set implies that the
Fréchet derivative at each interior point is "positive definite":
`⟨h, DT(u) h⟩ ≥ α ‖h‖²`.
-/
theorem fderiv_inner_lower_bound
    {s : Set V} (hs_open : IsOpen s)
    {T : V → V} {α : ℝ} (_hα : 0 < α)
    (hT_mono : IsStronglyMonotoneOn T s α)
    (hT_C1 : ContDiffOn ℝ 1 T s)
    (u : V) (hu : u ∈ s) (h : V) :
    α * ‖h‖ ^ 2 ≤ inner ℝ h (fderiv ℝ T u h) := by
  -- By strong monotonicity applied to u and u + t h:
  have h_ineq : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), α * t^2 * ‖h‖^2 ≤ t * inner ℝ h (T (u + t • h) - T u) := by
    -- By strong monotonicity, we have α * ‖t • h‖^2 ≤ inner ℝ (t • h) (T (u + t • h) - T u).
    have h_ineq : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), α * ‖t • h‖^2 ≤ inner ℝ (t • h) (T (u + t • h) - T u) := by
      -- By definition of strong monotonicity, we have
      have h_strong_mono : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), u + t • h ∈ s := by
        exact mem_nhdsWithin_of_mem_nhds ( ContinuousAt.preimage_mem_nhds ( show ContinuousAt ( fun t : ℝ => u + t • h ) 0 by fun_prop ) ( hs_open.mem_nhds <| by simpa ) );
      filter_upwards [ h_strong_mono ] with t ht using by simpa using hT_mono ( u + t • h ) ht u hu;
    simp_all +decide [ norm_smul, mul_pow, mul_assoc, inner_smul_left ];
  -- Since $T$ is C1 at $u$, the difference quotient converges to $DT(u) h$.
  have h_diff_quot : Filter.Tendsto (fun t : ℝ => (1 / t) • (T (u + t • h) - T u)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (fderiv ℝ T u h)) := by
    have h_deriv : HasDerivAt (fun t : ℝ => T (u + t • h)) (fderiv ℝ T u h) 0 := by
      have h_cont_diff : ContDiffAt ℝ 1 T u := by
        exact hT_C1.contDiffAt ( hs_open.mem_nhds hu )
      have h_deriv : HasDerivAt (fun t : ℝ => T (u + t • h)) (fderiv ℝ T u h) 0 := by
        have h_chain : HasDerivAt (fun t : ℝ => u + t • h) h 0 := by
          simpa using hasDerivAt_id ( 0 : ℝ ) |> HasDerivAt.smul_const <| h
        convert HasFDerivAt.comp_hasDerivAt _ _ h_chain using 1;
        simpa using h_cont_diff.differentiableAt ( by norm_num ) |> DifferentiableAt.hasFDerivAt;
      exact h_deriv;
    simpa [ div_eq_inv_mul ] using h_deriv.tendsto_slope_zero_right;
  nontriviality;
  have h_lim_ineq : Filter.Tendsto (fun t : ℝ => α * t * ‖h‖^2) (nhdsWithin 0 (Set.Ioi 0)) (nhds (α * 0 * ‖h‖^2)) ∧ Filter.Tendsto (fun t : ℝ => inner ℝ h ((1 / t) • (T (u + t • h) - T u))) (nhdsWithin 0 (Set.Ioi 0)) (nhds (inner ℝ h (fderiv ℝ T u h))) := by
    exact ⟨ tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by simp +decide ), Filter.Tendsto.inner tendsto_const_nhds h_diff_quot ⟩;
  have h_lim_ineq : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), α * ‖h‖^2 ≤ inner ℝ h ((1 / t) • (T (u + t • h) - T u)) := by
    filter_upwards [ h_ineq, self_mem_nhdsWithin ] with t ht ht' using by rw [ inner_smul_right ] ; rw [ one_div, mul_comm ] ; rw [ inv_mul_eq_div, le_div_iff₀ ] <;> nlinarith [ ht'.out ] ;
  exact le_of_tendsto_of_tendsto tendsto_const_nhds ( by tauto ) h_lim_ineq
/-
The derivative of a strongly monotone C¹ map is surjective
at each interior point (positive-definite ⇒ injective ⇒
surjective in finite dimensions).
-/
theorem fderiv_range_eq_top [FiniteDimensional ℝ V]
    {s : Set V} (hs_open : IsOpen s)
    {T : V → V} {α : ℝ} (hα : 0 < α)
    (hT_mono : IsStronglyMonotoneOn T s α)
    (hT_C1 : ContDiffOn ℝ 1 T s)
    (u : V) (hu : u ∈ s) :
    (↑(fderiv ℝ T u) : V →ₗ[ℝ] V).range = ⊤ := by
  refine' Submodule.eq_top_of_finrank_eq _;
  refine' LinearMap.finrank_range_of_inj _;
  refine' fun x y hxy => _;
  have := fderiv_inner_lower_bound hs_open hα hT_mono hT_C1 u hu ( x - y ) ; simp_all +decide ;
  exact sub_eq_zero.mp ( norm_eq_zero.mp ( by contrapose! this; positivity ) )
/-- The image `T '' s` is open (inverse function theorem). -/
theorem image_isOpen [FiniteDimensional ℝ V]
    {s : Set V} (hs_open : IsOpen s)
    {T : V → V} {α : ℝ} (hα : 0 < α)
    (hT_mono : IsStronglyMonotoneOn T s α)
    (hT_C1 : ContDiffOn ℝ 1 T s) :
    IsOpen (T '' s) := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  obtain ⟨u, hu, rfl⟩ := hy
  have hcd : ContDiffAt ℝ 1 T u := hT_C1.contDiffAt (hs_open.mem_nhds hu)
  have hstrict : HasStrictFDerivAt T (fderiv ℝ T u) u :=
    hcd.hasStrictFDerivAt (by norm_num)
  have hmap : Filter.map T (nhds u) = nhds (T u) :=
    hstrict.map_nhds_eq_of_surj (fderiv_range_eq_top hs_open hα hT_mono hT_C1 u hu)
  rw [← hmap]
  exact Filter.image_mem_map (hs_open.mem_nhds hu)
/-
The image `T '' s` is closed (strong monotonicity ⇒ Cauchy sequences
in the image lift to Cauchy sequences in `s`, boundary coercivity keeps
the limit inside `s`).
-/
theorem image_isClosed [FiniteDimensional ℝ V]
    {s : Set V} (hs_open : IsOpen s)
    {T : V → V} (hT_cont : ContinuousOn T s)
    {α : ℝ} (hα : 0 < α)
    (hT_mono : IsStronglyMonotoneOn T s α)
    (hT_coercive : ∀ x ∈ frontier s,
      Filter.Tendsto (fun u => ‖T u‖) (nhdsWithin x s) Filter.atTop) :
    IsClosed (T '' s) := by
  refine' isClosed_iff_clusterPt.mpr fun x hx => _;
  -- By definition of cluster point, there exists a sequence $(u_n)$ in $s$ such that $T(u_n) \to x$.
  obtain ⟨u_n, hu_n_s, hu_n_T⟩ : ∃ (u_n : ℕ → V), (∀ n, u_n n ∈ s) ∧ Filter.Tendsto (fun n => T (u_n n)) Filter.atTop (nhds x) := by
    rw [ clusterPt_principal_iff ] at hx;
    choose u hu using fun n : ℕ => hx ( Metric.ball x ( 1 / ( n + 1 ) ) ) ( Metric.ball_mem_nhds x ( by positivity ) );
    choose v hv using fun n => hu n |>.2;
    exact ⟨ v, fun n => ( hv n ).1, by simpa only [ hv ] using tendsto_iff_dist_tendsto_zero.mpr <| squeeze_zero ( fun _ => dist_nonneg ) ( fun n => le_of_lt <| hu n |>.1 ) <| tendsto_one_div_add_atTop_nhds_zero_nat ⟩;
  -- Since $(u_n)$ is Cauchy, it converges to some $u^* \in V$.
  obtain ⟨u_star, hu_star⟩ : ∃ u_star : V, Filter.Tendsto u_n Filter.atTop (nhds u_star) := by
    have h_cauchy : CauchySeq u_n := by
      have h_cauchy : ∀ m n, ‖u_n m - u_n n‖ ≤ (1 / α) * ‖T (u_n m) - T (u_n n)‖ := by
        intro m n
        have h_cauchy : α * ‖u_n m - u_n n‖ ^ 2 ≤ inner ℝ (u_n m - u_n n) (T (u_n m) - T (u_n n)) := by
          exact hT_mono _ ( hu_n_s m ) _ ( hu_n_s n )
        have h_cauchy' : α * ‖u_n m - u_n n‖ ≤ ‖T (u_n m) - T (u_n n)‖ := by
          nlinarith [ norm_nonneg ( u_n m - u_n n ), norm_nonneg ( T ( u_n m ) - T ( u_n n ) ), abs_le.mp ( abs_real_inner_le_norm ( u_n m - u_n n ) ( T ( u_n m ) - T ( u_n n ) ) ) ]
        field_simp [hα] at h_cauchy' ⊢
        exact h_cauchy';
      rw [ Metric.cauchySeq_iff ];
      exact fun ε εpos => by rcases Metric.cauchySeq_iff.1 ( hu_n_T.cauchySeq ) ( ε / ( 1 / α ) ) ( div_pos εpos ( one_div_pos.mpr hα ) ) with ⟨ N, hN ⟩ ; exact ⟨ N, fun m hm n hn => by rw [ dist_eq_norm ] ; exact lt_of_le_of_lt ( h_cauchy m n ) ( by have := hN m hm n hn; rw [ dist_eq_norm ] at this; rw [ lt_div_iff₀' ( one_div_pos.mpr hα ) ] at this; linarith ) ⟩ ;
    exact cauchySeq_tendsto_of_complete h_cauchy;
  -- Since $u^* \in \overline{s}$ and $s$ is open, we have $u^* \in s$ or $u^* \in \partial s$.
  by_cases hu_star_boundary : u_star ∈ frontier s;
  · have := hT_coercive u_star hu_star_boundary;
    exact absurd ( this.comp ( show Filter.Tendsto u_n Filter.atTop ( nhdsWithin u_star s ) from Filter.tendsto_inf.2 ⟨ hu_star, Filter.tendsto_principal.2 <| Filter.Eventually.of_forall hu_n_s ⟩ ) ) ( not_tendsto_atTop_of_tendsto_nhds <| hu_n_T.norm );
  · -- Since $u^* \in \overline{s}$ and $s$ is open, we have $u^* \in s$.
    have hu_star_in_s : u_star ∈ s := by
      simp_all +decide [ frontier_eq_closure_inter_closure ];
      exact hu_star_boundary ( mem_closure_of_tendsto hu_star ( Filter.Eventually.of_forall hu_n_s ) );
    exact ⟨ u_star, hu_star_in_s, tendsto_nhds_unique ( hT_cont.continuousAt ( hs_open.mem_nhds hu_star_in_s ) |> fun h => h.tendsto.comp hu_star ) hu_n_T ⟩
/-
**Corrected Minty-style existence (specialized).** A C¹, strongly
monotone, boundary-coercive map on an open convex non-empty subset of
a finite-dimensional Hilbert space has a unique zero.
Compared to the original (false) statement, we require strong monotonicity
(with constant `α > 0`) and C¹ regularity, which together enable the
inverse function theorem argument for openness of the image.
-/
theorem exists_unique_zero_of_stronglyMonotone_C1_coercive
    [FiniteDimensional ℝ V]
    {s : Set V} (hs_open : IsOpen s) (_hs_conv : Convex ℝ s)
    (hs_nonempty : s.Nonempty)
    {T : V → V} (hT_cont : ContinuousOn T s)
    {α : ℝ} (hα : 0 < α)
    (hT_mono : IsStronglyMonotoneOn T s α)
    (hT_C1 : ContDiffOn ℝ 1 T s)
    (hT_coercive : ∀ x ∈ frontier s,
      Filter.Tendsto (fun u => ‖T u‖) (nhdsWithin x s) Filter.atTop) :
    ∃! u, u ∈ s ∧ T u = 0 := by
  -- T '' s is nonempty: pick u₀ from hs_nonempty, then T u₀ ∈ T '' s.
  have h_nonempty : T '' s = Set.univ := by
    have h_image : IsClopen (T '' s) := by
      exact ⟨image_isClosed hs_open hT_cont hα hT_mono hT_coercive,
             image_isOpen hs_open hα hT_mono hT_C1⟩;
    exact IsClopen.eq_univ h_image ( Set.Nonempty.image _ hs_nonempty );
  obtain ⟨ u, hu₁, hu₂ ⟩ := show ∃ u ∈ s, T u = 0 from by simpa using Set.ext_iff.mp h_nonempty 0;
  refine' ⟨ u, ⟨ hu₁, hu₂ ⟩, fun v ⟨ hv₁, hv₂ ⟩ => _ ⟩;
  have := hT_mono v hv₁ u hu₁; simp_all +decide ;
  exact sub_eq_zero.mp ( norm_eq_zero.mp ( by contrapose! this; positivity ) )
/- The original theorem statement below is **false** as stated.
   Counterexample: `V = ℝ`, `s = Set.univ`, `T u = Real.exp u`.
   `frontier Set.univ = ∅` makes the coercivity condition vacuously true,
   `T` is strictly monotone and continuous, but `exp u > 0` has no zero.
   See `exists_unique_zero_of_stronglyMonotone_C1_coercive` above for the
   corrected version with additional hypotheses. -/
/- theorem exists_unique_zero_of_strict_monotone_continuous_coercive
    [FiniteDimensional ℝ V]
    {s : Set V} (hs_open : IsOpen s) (_hs_conv : Convex ℝ s)
    (_hs_nonempty : s.Nonempty)
    {T : V → V} (_hT_cont : ContinuousOn T s)
    (_hT_mono : IsStrictMonotoneOn T s)
    (_hT_coercive : ∀ x ∈ frontier s,
      Filter.Tendsto (fun u => ‖T u‖) (nhdsWithin x s) Filter.atTop) :
    ∃! u, u ∈ s ∧ T u = 0 := sorry -/
end Irn
