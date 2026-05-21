/-
# Barriers (paper §2.1)

Logarithmically homogeneous self-concordant barriers (LHSCB) and the
conjugate barrier-gradient maps `F*`, `G*`, `φ`.

This pass exposes only the LHSCB consequences the rest of the
formalisation actually needs, plus a sum operation:

* the Euler identity `⟨u, ∇f(u)⟩ = -ν` (logarithmic homogeneity of
  degree `-ν`),
* gradient monotonicity (convexity of `f`),
* `LHSCB.add`: the sum of a `ν₁`-LHSCB and a `ν₂`-LHSCB is a
  `(ν₁+ν₂)`-LHSCB on the intersection of their domains.

Smoothness, the third-derivative self-concordance bound, and the
`(Hess f)⁻¹`-dual-norm gradient bound are deferred — the dual-norm
bound applies to the IRN setup's combined `F = f + g` only and is
carried at the `IrnSetup` level since it does not decompose.

Paper references:
* Definition 2 (`ν`-LHSCB)
* Eq. (2.2) (Euler identity)
* §2.1 (conjugate barriers)
-/

import Mathlib.Analysis.InnerProductSpace.Basic

namespace Irn

open scoped InnerProductSpace

/-- An abstract `ν`-LHSCB on a real inner product space. We record
only the gradient, the domain, and the two Euler / convexity
consequences that the IRN analysis consumes through sums. The barrier
function `f` itself is kept around so a concrete instance can attach a
potential. -/
structure LHSCB (V : Type*)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] (ν : ℕ) where
  /-- The barrier function. -/
  f : V → ℝ
  /-- The gradient `∇f`. -/
  grad : V → V
  /-- The barrier domain — intended to be the (topological) interior of
  the associated convex cone. An LHSCB is defined only on the interior
  of its cone, since the barrier blows up on the boundary. -/
  domain : Set V
  /-- The domain is open (an LHSCB is defined on the interior of a
  convex cone, which is open). -/
  domain_open : IsOpen domain
  /-- **Euler identity.** Logarithmic homogeneity of degree `-ν`
  implies `⟨u, ∇f(u)⟩ = -ν` for every `u ∈ domain`. -/
  euler : ∀ u ∈ domain, inner ℝ u (grad u) = -(ν : ℝ)
  /-- **Gradient monotonicity.** Convexity of `f` implies the gradient
  map is monotone on `domain`. -/
  grad_monotone : ∀ u ∈ domain, ∀ v ∈ domain,
    0 ≤ inner ℝ (u - v) (grad u - grad v)

namespace LHSCB

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Sum of LHSCBs.** A `ν₁`-LHSCB plus a `ν₂`-LHSCB is a
`(ν₁+ν₂)`-LHSCB on the intersection of their domains; Euler and
gradient monotonicity are both additive. -/
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

@[simp] theorem add_grad {ν₁ ν₂ : ℕ} (f : LHSCB V ν₁) (g : LHSCB V ν₂)
    (u : V) : (f.add g).grad u = f.grad u + g.grad u := rfl

@[simp] theorem add_domain {ν₁ ν₂ : ℕ} (f : LHSCB V ν₁) (g : LHSCB V ν₂) :
    (f.add g).domain = f.domain ∩ g.domain := rfl

end LHSCB

end Irn
