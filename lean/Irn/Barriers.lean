/-
# Barriers (paper §2.1)

Logarithmically homogeneous self-concordant barriers (LHSCB) and the
conjugate barrier-gradient maps `F*`, `G*`, `φ`.

This pass exposes the LHSCB consequences the rest of the formalisation
needs, plus a sum operation. The barrier function `f` and its gradient
`grad` are defined on all of `V`, but only their values on the open
`domain` (intended to be the interior of an associated convex cone)
are constrained and meaningful.

Recorded properties:

* `euler` — `⟨u, ∇f(u)⟩ = -ν` on `domain` (the differentiated form of
  log-homogeneity);
* `grad_monotone` — convexity of `f`, as gradient monotonicity;
* `log_homog` — `f(λ x) = f(x) - ν log λ` for `x ∈ domain` and `λ > 0`
  (the log-homogeneity from which `euler` is derivable);
* `LHSCB.add` — the sum of a `ν₁`-LHSCB and a `ν₂`-LHSCB is a
  `(ν₁+ν₂)`-LHSCB on the intersection of their domains.

**Deferred to future commits:**

* `K : Set V` as a structural parameter (the convex cone of which
  `domain` is the interior). Currently we carry only `domain` and its
  openness; the cone is implicit.
* Strict convexity on `domain` (captured by a separate predicate
  `LHSCB.IsStrict`; not always satisfied by lifted barriers).
* The barrier property `f(x) → +∞` at `∂K` (requires knowing `K`).
* The third-derivative self-concordance bound (requires Mathlib's
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

/-- An abstract `ν`-LHSCB on a real inner product space `V`. The
domain (an open set) is intended to be the interior of an associated
convex cone; the constraints are imposed only there. -/
structure LHSCB (V : Type*)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] (ν : ℕ) where
  /-- The barrier function. -/
  f : V → ℝ
  /-- The gradient `∇f`. -/
  grad : V → V
  /-- The (open) barrier domain — intended to be `interior K` for the
  associated cone `K`. -/
  domain : Set V
  /-- The domain is open. -/
  domain_open : IsOpen domain
  /-- **Euler identity** (differentiated logarithmic homogeneity):
  `⟨u, ∇f(u)⟩ = -ν` on `domain`. -/
  euler : ∀ u ∈ domain, inner ℝ u (grad u) = -(ν : ℝ)
  /-- **Gradient monotonicity** on `domain` (convexity of `f`). -/
  grad_monotone : ∀ u ∈ domain, ∀ v ∈ domain,
    0 ≤ inner ℝ (u - v) (grad u - grad v)
  /-- **Logarithmic homogeneity of degree `-ν`**:
  `f(t · x) = f(x) - ν · log t` for every `x ∈ domain` and `t > 0`.
  Requires `t • x ∈ domain` (true when `domain` is the interior of a
  cone: cones are closed under positive scalar multiplication and the
  interior is too). -/
  log_homog : ∀ x ∈ domain, ∀ t : ℝ, 0 < t →
    f (t • x) = f x - (ν : ℝ) * Real.log t

namespace LHSCB

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Sum of LHSCBs.** A `ν₁`-LHSCB plus a `ν₂`-LHSCB is a
`(ν₁+ν₂)`-LHSCB on the intersection of their domains. -/
def add {ν₁ ν₂ : ℕ} (f : LHSCB V ν₁) (g : LHSCB V ν₂) :
    LHSCB V (ν₁ + ν₂) where
  f := fun v => f.f v + g.f v
  grad := fun v => f.grad v + g.grad v
  domain := f.domain ∩ g.domain
  domain_open := f.domain_open.inter g.domain_open
  euler := by
    rintro u ⟨hu_f, hu_g⟩
    rw [inner_add_right, f.euler u hu_f, g.euler u hu_g]
    push_cast
    ring
  grad_monotone := by
    rintro u ⟨hu_f, hu_g⟩ v ⟨hv_f, hv_g⟩
    have hf := f.grad_monotone u hu_f v hv_f
    have hg := g.grad_monotone u hu_g v hv_g
    have h : (f.grad u + g.grad u) - (f.grad v + g.grad v) =
        (f.grad u - f.grad v) + (g.grad u - g.grad v) := by abel
    rw [h, inner_add_right]
    linarith
  log_homog := by
    rintro x ⟨hx_f, hx_g⟩ t ht
    show f.f (t • x) + g.f (t • x) =
        f.f x + g.f x - ((ν₁ + ν₂ : ℕ) : ℝ) * Real.log t
    rw [f.log_homog x hx_f t ht, g.log_homog x hx_g t ht]
    push_cast
    ring

@[simp] theorem add_grad {ν₁ ν₂ : ℕ} (f : LHSCB V ν₁) (g : LHSCB V ν₂)
    (u : V) : (f.add g).grad u = f.grad u + g.grad u := rfl

@[simp] theorem add_domain {ν₁ ν₂ : ℕ} (f : LHSCB V ν₁) (g : LHSCB V ν₂) :
    (f.add g).domain = f.domain ∩ g.domain := rfl

end LHSCB

end Irn
