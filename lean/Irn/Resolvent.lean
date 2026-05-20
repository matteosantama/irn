/-
# Closed-form resolvent (paper §4)

The non-linear set-valued operator `Ψ = Q + μ ∂G*` and the
closed-form variable-metric resolvent (Theorem 8). We also state
the maximal monotone extension auxiliary lemma (Lemma A.1).

Paper references:
* Theorem 8 (closed-form resolvent of `Ψ`)
* Appendix Lemma A.1 (maximal monotone extension)
-/

import Irn.Sphere

namespace Irn

open scoped InnerProductSpace

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  (𝓢 : IrnSetup H)

/-- The graph of `Ψ = Q + μ ∂G*`, treated as a relation on `H × H`.
We model `Ψ` as a set-valued operator via its graph. -/
def graphPsi (μ : ℝ) : Set (H × H) := sorry

/-- The `H`-metric resolvent `J^H_Ψ(z) = (H + Ψ)⁻¹(H z)`. -/
def resolvent (μ : ℝ) (Hmat : H →L[ℝ] H) (z : H) : H := sorry

/-- **Theorem 8 (Closed-form resolvent of `Ψ`).** For every `μ > 0`,
every self-adjoint positive-definite preconditioner `H ≻ 0`, and
every `z ∈ H`, the resolvent value `u = J^H_Ψ(z)` lies in `Cplus` and
is given in closed form by
`u = (H + M)⁻¹(H z + θ e_τ)`, where `θ` is the positive root of an
explicit scalar quadratic. -/
theorem resolvent_closed_form
    (μ : ℝ) (hμ : 0 < μ) (Hmat : H →L[ℝ] H) (z : H) :
    True := sorry  -- placeholder; the precise statement needs the
                   -- `M`, `e_τ`, and `P` data, which are not abstracted
                   -- in this first pass.

/-- **Lemma A.1 (Maximal monotone extension).** A continuous monotone
single-valued operator on an open convex set extends to a maximally
monotone operator on the ambient Hilbert space. -/
theorem exists_maximal_monotone_extension
    {H₀ : Set H} (hH₀_open : IsOpen H₀) (hH₀_convex : Convex ℝ H₀)
    (Q : H → H) (hQ_cont : ContinuousOn Q H₀)
    (hQ_mono : ∀ u ∈ H₀, ∀ v ∈ H₀, 0 ≤ inner ℝ (u - v) (Q u - Q v)) :
    True := sorry  -- placeholder: requires the maximal-monotone API
                   -- (graph, extension), which we have not yet imported.

end Irn
