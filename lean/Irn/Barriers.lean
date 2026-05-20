/-
# Barriers (paper §2.1)

Logarithmically homogeneous self-concordant barriers (LHSCB) and the
conjugate barrier-gradient maps `F*`, `G*`, `φ`.

This pass exposes only the three LHSCB consequences the rest of the
formalisation actually needs:

* the Euler identity `⟨u, ∇f(u)⟩ = -ν` (logarithmic homogeneity of
  degree `-ν`),
* gradient monotonicity (convexity of `f`),
* the LHSCB gradient bound `‖∇f(u)‖_dual ≤ √ν` in an abstract dual
  norm (intended to be `‖·‖_{(Hess f)⁻¹}` or a preconditioned variant
  such as the IRN weighting `W = I + ∇²f`).

Smoothness and the third-derivative self-concordance bound are deferred.

Paper references:
* Definition 2 (`ν`-LHSCB)
* Eq. (2.2) (Euler identity)
* §2.1 (conjugate barriers)
-/

import Mathlib.Analysis.InnerProductSpace.Basic

namespace Irn

open scoped InnerProductSpace

/-- An abstract `ν`-LHSCB on a finite-dimensional real inner product
space. We record only the gradient, the domain, and the three Euler /
convexity / dual-norm consequences that the IRN analysis actually
consumes. The barrier function `f` itself is kept around so that
downstream refinements can attach a concrete potential.

The `dualNorm` field is intended to be `‖·‖_{(Hess f)⁻¹}` (or the
preconditioned `‖·‖_{(I + Hess f)⁻¹}` used by the IRN method); we keep
it abstract so an instance can choose either. -/
structure LHSCB (V : Type*)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] (ν : ℕ) where
  /-- The barrier function. -/
  f : V → ℝ
  /-- The gradient `∇f`. -/
  grad : V → V
  /-- The (open) barrier domain. -/
  domain : Set V
  /-- **Euler identity.** Logarithmic homogeneity of degree `-ν`
  implies `⟨u, ∇f(u)⟩ = -ν` for every `u ∈ domain`. -/
  euler : ∀ u ∈ domain, inner ℝ u (grad u) = -(ν : ℝ)
  /-- **Gradient monotonicity.** Convexity of `f` implies the gradient
  map is monotone on `domain`. -/
  grad_monotone : ∀ u ∈ domain, ∀ v ∈ domain,
    0 ≤ inner ℝ (u - v) (grad u - grad v)
  /-- Auxiliary dual norm `‖·‖_{(Hess f)⁻¹}` (or a preconditioned
  variant). Kept abstract to accommodate the IRN `W = I + Hess F`
  weighting. -/
  dualNorm : V → V → ℝ
  /-- **LHSCB gradient bound.** `‖∇f(u)‖_dual ≤ √ν` on the domain.
  In the unpreconditioned case (`dualNorm = ‖·‖_{(Hess f)⁻¹}`) this is
  the classical bound; with `W = I + Hess f` preconditioning, `W⁻¹ ⪯
  (Hess f)⁻¹` makes the W-norm no larger, so the bound transports. -/
  dualNorm_grad_bound : ∀ u ∈ domain, dualNorm u (grad u) ≤ Real.sqrt (ν : ℝ)

end Irn
