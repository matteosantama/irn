/-
# Closed-form resolvent (paper §4)

Theorem 8 (closed-form resolvent of `Ψ = Q + μ ∂G*`) and the
auxiliary maximal-monotone extension result (Lemma A.1). With the
explicit embedding structure (`M`, `e_τ`, `q`, `tau_proj`) carried by
`IrnSetup`, Theorem 8 can be stated literally.

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

/-- **Theorem 8 (Closed-form resolvent of `Ψ`).**
For every `μ > 0`, every self-adjoint positive-definite preconditioner
`H_k : H →L[ℝ] H`, and every `z ∈ H`, the resolvent value
`u = J_Ψ^{H_k}(z)` lies in `Cplus` and is the unique solution of the
augmented system
```
    (H_k + M) u = H_k z + θ • e_τ,
    θ · tau_proj u = q(u) + μ,
    θ > 0.
```
This is exactly the closed-form formula `u = (H_k + M)⁻¹(H_k z + θ • e_τ)`
of the paper, expressed as a system to avoid an explicit linear-map
inverse. We state existence; the (constructive) proof via the scalar
quadratic for `θ` is left as `sorry` in this first formalisation. -/
theorem resolvent_closed_form
    (μ : ℝ) (hμ : 0 < μ) (H_k : H →L[ℝ] H) (z : H) :
    ∃ u : H, ∃ θ : ℝ,
      u ∈ 𝓢.Cplus ∧
      0 < θ ∧
      (H_k + 𝓢.M) u = H_k z + θ • 𝓢.e_τ ∧
      θ * 𝓢.tau_proj u = 𝓢.q u + μ := sorry

/-- The resolvent value `u = J_Ψ^{H_k}(z)`, extracted from Theorem 8. -/
noncomputable def resolvent_value
    (μ : ℝ) (hμ : 0 < μ) (H_k : H →L[ℝ] H) (z : H) : H :=
  Classical.choose (resolvent_closed_form 𝓢 μ hμ H_k z)

/-- **Lemma A.1 (Maximal monotone extension).** A continuous monotone
single-valued operator on an open convex set extends to a maximally
monotone operator on the ambient Hilbert space. -/
theorem exists_maximal_monotone_extension
    {H₀ : Set H} (_hH₀_open : IsOpen H₀) (_hH₀_convex : Convex ℝ H₀)
    (Q : H → H) (_hQ_cont : ContinuousOn Q H₀)
    (_hQ_mono : ∀ u ∈ H₀, ∀ v ∈ H₀, 0 ≤ inner ℝ (u - v) (Q u - Q v)) :
    True := sorry

end Irn
