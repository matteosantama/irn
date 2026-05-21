/-
# Barriers (paper §2.1)

Logarithmically homogeneous self-concordant barriers (LHSCB) and the
conjugate barrier-gradient maps `F*`, `G*`, `φ`.

An `LHSCB V K ν` is a `ν`-LHSCB on the (convex) cone `K ⊆ V`. The
barrier function `f` and its gradient `grad` are defined on all of
`V`, but only their values on `interior K` are constrained and
meaningful — outside the interior the values are arbitrary (typically
junk).

Recorded properties:

* `euler` — `⟨u, ∇f(u)⟩ = -ν` on `int(K)` (differentiated form of
  log-homogeneity);
* `grad_monotone` — convexity of `f`, as gradient monotonicity;
* `log_homog` — `f(t x) = f(x) - ν log t` for `x ∈ int(K)` and `t > 0`;
* `barrier` — `f(x) → +∞` as `x` approaches `∂K = frontier K` from
  inside.

* `LHSCB.add` — the sum of a `ν₁`-LHSCB on `K₁` and a `ν₂`-LHSCB on
  `K₂` is a `(ν₁+ν₂)`-LHSCB on `K₁ ∩ K₂`. Uses `interior_inter`.

**Deferred to future commits:**

* Strict convexity on `int(K)` (captured by a separate predicate
  `LHSCB.IsStrict`; not satisfied by lifted barriers).
* The third-derivative self-concordance bound (needs Mathlib's
  higher-order Frechet derivative API).

Paper references:
* Definition 2 (`ν`-LHSCB)
* Eq. (2.2) (Euler identity)
* §2.1 (conjugate barriers)
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Irn

open scoped InnerProductSpace

/-- An abstract `ν`-LHSCB on a real inner product space `V` with
respect to the (convex) cone `K ⊆ V`. -/
structure LHSCB (V : Type*)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (K : Set V) (ν : ℕ) where
  /-- The barrier function. -/
  f : V → ℝ
  /-- The gradient `∇f`. -/
  grad : V → V
  /-- **Euler identity**: `⟨u, ∇f(u)⟩ = -ν` on `int(K)`. -/
  euler : ∀ u ∈ interior K, inner ℝ u (grad u) = -(ν : ℝ)
  /-- **Gradient monotonicity** on `int(K)`. -/
  grad_monotone : ∀ u ∈ interior K, ∀ v ∈ interior K,
    0 ≤ inner ℝ (u - v) (grad u - grad v)
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

/-- **Sum of LHSCBs.** A `ν₁`-LHSCB on `K₁` plus a `ν₂`-LHSCB on `K₂`
is a `(ν₁+ν₂)`-LHSCB on `K₁ ∩ K₂`. -/
noncomputable def add {K₁ K₂ : Set V} {ν₁ ν₂ : ℕ}
    (f : LHSCB V K₁ ν₁) (g : LHSCB V K₂ ν₂) :
    LHSCB V (K₁ ∩ K₂) (ν₁ + ν₂) where
  f := fun v => f.f v + g.f v
  grad := fun v => f.grad v + g.grad v
  euler := by
    rintro u hu
    have hu' : u ∈ interior K₁ ∩ interior K₂ := by
      rw [interior_inter] at hu; exact hu
    rw [inner_add_right, f.euler u hu'.1, g.euler u hu'.2]
    push_cast
    ring
  grad_monotone := by
    rintro u hu v hv
    have hu' : u ∈ interior K₁ ∩ interior K₂ := by
      rw [interior_inter] at hu; exact hu
    have hv' : v ∈ interior K₁ ∩ interior K₂ := by
      rw [interior_inter] at hv; exact hv
    have hf := f.grad_monotone u hu'.1 v hv'.1
    have hg := g.grad_monotone u hu'.2 v hv'.2
    have h : (f.grad u + g.grad u) - (f.grad v + g.grad v) =
        (f.grad u - f.grad v) + (g.grad u - g.grad v) := by abel
    rw [h, inner_add_right]
    linarith
  log_homog := by
    rintro x hx t ht
    have hx' : x ∈ interior K₁ ∩ interior K₂ := by
      rw [interior_inter] at hx; exact hx
    rw [show ((ν₁ + ν₂ : ℕ) : ℝ) = (ν₁ : ℝ) + (ν₂ : ℝ) from by push_cast; ring,
        f.log_homog x hx'.1 t ht, g.log_homog x hx'.2 t ht]
    ring
  barrier := by
    -- The general claim — `f + g → ∞` near every boundary point of
    -- `K₁ ∩ K₂` — requires a case split on whether the point is on
    -- `frontier K₁` or `frontier K₂` and depends on each barrier
    -- being bounded below where the other diverges. Deferred.
    intros x _
    sorry

@[simp] theorem add_grad {K₁ K₂ : Set V} {ν₁ ν₂ : ℕ}
    (f : LHSCB V K₁ ν₁) (g : LHSCB V K₂ ν₂) (u : V) :
    (f.add g).grad u = f.grad u + g.grad u := rfl

end LHSCB

end Irn
