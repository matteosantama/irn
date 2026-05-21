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
    -- Case-split on whether the frontier point lies in `frontier K₁`
    -- or `frontier K₂`. Requires each barrier being bounded below on
    -- the other cone's interior (from convexity via the derived
    -- `grad_monotone`). Deferred.
    intros x _
    sorry

/-- **Derived gradient of a sum.** `(f.add g).grad x = f.grad x +
g.grad x` on `int(K₁ ∩ K₂)`. Follows from `fderiv.add` (Mathlib's
`fderiv_add` requires `DifferentiableAt`, which comes from each
`contDiff` at points in the respective interiors) and linearity of
Riesz representation.

Sorried — the derivation is mechanical but requires assembling
several Mathlib pieces (`HasFDerivAt.add`, `LinearIsometryEquiv.map_add`
on `toDual.symm`). -/
theorem add_grad {K₁ K₂ : Set V} {ν₁ ν₂ : ℕ}
    (f : LHSCB V K₁ ν₁) (g : LHSCB V K₂ ν₂)
    {u : V} (_hu : u ∈ interior K₁ ∩ interior K₂) :
    (f.add g).grad u = f.grad u + g.grad u := by
  sorry

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
`t = 1`. The chain rule for `fun t => f(t · u)` gives a derivative
`⟨u, ∇f(u)⟩` at `t = 1`; the RHS derivative is `-ν · (1/t) = -ν`.

Currently sorried. -/
theorem euler {K : Set V} {ν : ℕ} (f : LHSCB V K ν) :
    ∀ u ∈ interior K, inner ℝ u (f.grad u) = -(ν : ℝ) := by
  intro u _hu
  sorry

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
