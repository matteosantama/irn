/-
# Monotone operator theory

Predicates and basic API for monotone (and strictly monotone) operators
on Hilbert spaces, plus a specialized Minty-style existence theorem
for continuous strictly monotone coercive operators on open convex
domains in finite-dimensional Hilbert spaces.

This is the minimal setup needed to discharge the existence half of
`exists_unique_centralPath` (paper Theorem 5) via Minty's resolvent
theorem.

The classical Minty theorem says: every maximal monotone operator on a
Hilbert space has resolvents `(I + λT)⁻¹` everywhere defined. We work
in the more concrete setting where `T : V → V` is single-valued,
continuous, strictly monotone on an open convex set, and coercive at
the boundary; under these hypotheses there is a unique zero of `T` in
the open set.

Theorem statement currently sorried — the proof is via the variational
approach (minimize an energy `E_T` whose gradient is `T`) or via a
degree-theory argument. Both substantial; deferred to a follow-up.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

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

/-! ## Minty's existence theorem (specialized form) -/

/-- **Minty-style existence (specialized).** A continuous, strictly
monotone, boundary-coercive map on an open convex non-empty subset of
a finite-dimensional Hilbert space has a unique zero in the interior.

* `s` is open, convex, non-empty.
* `T : V → V` is continuous on `s`.
* `T` is strictly monotone on `s`.
* `T` is *boundary-coercive*: `‖T u‖ → ∞` as `u → x` within `s`, for
  every `x ∈ frontier s`. (For our IRN application, this comes from
  the LHSCB barrier `φ` blowing up at the boundary.)

Under these conditions, `∃! u ∈ s, T u = 0`. Equivalently, `T` is a
homeomorphism from `s` onto its image, which contains `0`.

**Proof outline (deferred):**
1. Strict monotonicity ⇒ `T` injective on `s`.
2. Approximate `T` by `T + ε I` (uniformly strictly monotone), which
   has a contraction-mapping fixed point in any bounded subset of `s`.
3. Compactness + Bolzano-Weierstrass extracts a convergent subsequence.
4. Boundary-coercivity ensures the limit stays in the interior.
5. Limit point satisfies `T(limit) = 0`.

Alternative proof: variational. Construct an energy `E : s → ℝ` with
`∇E = T`. Show `E` is strictly convex (from strict monotonicity) and
coercive at the boundary (from boundary-coercivity of `T`). The Direct
Method of the calculus of variations gives a unique minimum, which
satisfies `∇E = T = 0`. -/
theorem exists_unique_zero_of_strict_monotone_continuous_coercive
    [FiniteDimensional ℝ V]
    {s : Set V} (hs_open : IsOpen s) (_hs_conv : Convex ℝ s)
    (_hs_nonempty : s.Nonempty)
    {T : V → V} (_hT_cont : ContinuousOn T s)
    (_hT_mono : IsStrictMonotoneOn T s)
    (_hT_coercive : ∀ x ∈ frontier s,
      Filter.Tendsto (fun u => ‖T u‖) (nhdsWithin x s) Filter.atTop) :
    ∃! u, u ∈ s ∧ T u = 0 := sorry

end Irn
