/-
# Path-Following Complexity (paper §6)

The outer-loop analysis: tangentially-projected residual `tildeT`,
the on-sphere identity `P_u φ(u) = φ(u) + u`, the affine-in-`μ`
proximity-transfer identity, failure of Euclidean tolerances
(Proposition 12), the Hessian-norm proximity `δ`, the bounded
transfer constant (Lemma 13), the proximity transfer bound
(Lemma 14), the Hessian-norm quadratic contraction (Lemma 15), and
the polynomial complexity theorem (Theorem 16).

Paper references:
* Eq. (6.1) `P_u φ(u) = φ(u) + u`
* Eq. (6.3) transfer identity for `tildeT`
* Proposition 12 (failure of Euclidean tolerances)
* Remark 17 (power-law tolerances) — informal, no theorem
* Eq. (6.6) `W(u) = I + ∇²F*(u)`
* Eq. (6.7) Hessian-norm proximity `δ(u, μ)`
* Lemma 13 (bounded transfer constant)
* Lemma 14 (proximity transfer)
* Lemma 15 (Hessian-norm quadratic contraction)
* Theorem 16 (polynomial complexity)
-/

import Irn.RJN
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Irn

open scoped InnerProductSpace

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-! ## §6.3 Hessian-norm data.

`W(u) = I + ∇²F*(u)` and the `W(u)⁻¹`-weighted norm are recorded as
abstract stubs because the first-pass `IrnSetup` does not expose `F*`
as a potential with a computable Hessian. -/

/-- The Hessian metric `W(u) = I + ∇²F*(u)`, returned as a continuous
linear self-adjoint operator. Satisfies `W(u) ⪰ I`, hence is
invertible. -/
def W (𝓢 : IrnSetup H) (u : H) : H →L[ℝ] H := sorry

/-- The `W(u)⁻¹`-weighted norm. -/
noncomputable def normWinv (𝓢 : IrnSetup H) (u v : H) : ℝ := sorry

variable (𝓢 : IrnSetup H)

/-- The tangentially-projected residual `tildeT_μ(u) = P_u T_μ(u)`. -/
noncomputable def tildeT (μ : ℝ) (u : H) : H := proj u (T 𝓢 μ u)

/-! ## §6.1 Proximity transfer identity. -/

/-- **Eq. (6.1).** On `Sr ∩ int C`, the projector simplifies to
`P_u φ(u) = φ(u) + u`. -/
theorem proj_phi_on_sphere {u : H}
    (hS : u ∈ sphere 𝓢) (hC : u ∈ 𝓢.C) :
    proj u (𝓢.φ u) = 𝓢.φ u + u := by
  unfold proj
  rw [𝓢.inner_u_phi u hC]
  have huu : ‖u‖ ^ 2 = (𝓢.ν : ℝ) + 1 := by
    have hnorm : ‖u‖ = 𝓢.r := hS
    rw [hnorm, 𝓢.r_sq]
  rw [huu]
  have hpos : (0 : ℝ) < (𝓢.ν : ℝ) + 1 := by positivity
  rw [neg_div, div_self (ne_of_gt hpos), neg_smul, one_smul, sub_neg_eq_add]

/-- **Eq. (6.3).** Affine-in-`μ` proximity transfer identity for
`tildeT`. -/
theorem tildeT_transfer (μ σ : ℝ) (hμ : 0 < μ) (hσ : 0 < σ) {u : H}
    (hS : u ∈ sphere 𝓢) (hC : u ∈ 𝓢.C) :
    tildeT 𝓢 (σ * μ) u = tildeT 𝓢 μ u - ((1 - σ) * μ) • (𝓢.φ u + u) := sorry

/-! ## §6.2 Failure of Euclidean tolerances. -/

/-- The Euclidean transfer constant `R(u) = ‖φ(u) + u‖`. -/
noncomputable def R (u : H) : ℝ := ‖𝓢.φ u + u‖

/-- The identity `μ R(u*(μ)) = ‖Q(u*(μ))‖` from the proof of
Proposition 12. -/
theorem mu_R_eq_Q_norm {μ : ℝ} (hμ : 0 < μ) :
    μ * R 𝓢 (centralPathPoint 𝓢 μ hμ) =
      ‖𝓢.Q (centralPathPoint 𝓢 μ hμ)‖ := by
  set u := centralPathPoint 𝓢 μ hμ
  obtain ⟨_, hT⟩ := centralPathPoint_isCentralPathPoint 𝓢 μ hμ
  unfold T at hT
  unfold R
  have hT' : 𝓢.Q u + (μ • u + μ • 𝓢.φ u) = 0 := by
    rw [← add_assoc]; exact hT
  have hQ : 𝓢.Q u = -(μ • (𝓢.φ u + u)) := by
    have h1 : 𝓢.Q u = -(μ • u + μ • 𝓢.φ u) := add_eq_zero_iff_eq_neg.mp hT'
    rw [h1, smul_add, add_comm (μ • 𝓢.φ u)]
  rw [hQ, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hμ]

/-- **Proposition 12 (Failure of Euclidean tolerances).** For any
inner-loop tolerance function `f`, even a perfectly-centred iterate
`u_k = u*(μ_k)` requires `1 - σ_k = O(μ_k)` to keep the post-update
proximity inside any fixed-radius basin `ρ`. Polynomial complexity
`O(log(1/ε))` in the outer loop is unattainable with any Euclidean
tolerance.

We formalize the key identity at the central-path point: the
proximity `‖tildeT_{σμ}(u*(μ))‖ / (σμ)` equals
`(1 - σ)/σ · ‖Q(u*(μ))‖ / μ`, which is `Θ((1-σ)/μ)` since
`‖Q(u*(μ))‖ → ‖Q(u^∞)‖ > 0` in non-trivial instances. The
sub-linear schedule conclusion is left as a remark. -/
theorem euclidean_failure
    {μ : ℝ} (hμ : 0 < μ) {σ : ℝ} (hσ : 0 < σ) (hσ' : σ ≤ 1) :
    ‖tildeT 𝓢 (σ * μ) (centralPathPoint 𝓢 μ hμ)‖ / (σ * μ) =
      ((1 - σ) / σ) * (‖𝓢.Q (centralPathPoint 𝓢 μ hμ)‖ / μ) := sorry

/-! ## §6.3 Hessian-norm proximity. -/

/-- `W(u) ⪰ I`, i.e. `⟨v, W(u) v⟩ ≥ ‖v‖²`. -/
theorem W_ge_one (u : H) (v : H) :
    ‖v‖ ^ 2 ≤ inner ℝ v (W 𝓢 u v) := sorry

/-- Eq. (6.7). The Hessian-norm proximity
`δ(u, μ) = ‖tildeT_μ(u)‖_{W(u)⁻¹} / μ`. -/
noncomputable def delta (μ : ℝ) (u : H) : ℝ :=
  normWinv 𝓢 u (tildeT 𝓢 μ u) / μ

/-- **Lemma 13 (Bounded transfer constant).** For every
`u ∈ Sr ∩ int C`, `‖φ(u) + u‖_{W(u)⁻¹} ≤ 2 √(ν+1)`. -/
theorem transfer_bound {u : H}
    (hS : u ∈ sphere 𝓢) (hC : u ∈ 𝓢.C) :
    normWinv 𝓢 u (𝓢.φ u + u) ≤ 2 * Real.sqrt ((𝓢.ν : ℝ) + 1) := sorry

/-- **Lemma 14 (Proximity transfer).** Eq. (6.9):
`δ(u, σμ) ≤ δ(u, μ)/σ + 2(1-σ)√(ν+1)/σ` on `Sr ∩ int C`. -/
theorem proximity_transfer
    {μ : ℝ} (hμ : 0 < μ) {σ : ℝ} (hσ : 0 < σ) (hσ' : σ ≤ 1)
    {u : H} (hS : u ∈ sphere 𝓢) (hC : u ∈ 𝓢.C) :
    delta 𝓢 (σ * μ) u ≤
      delta 𝓢 μ u / σ +
        2 * (1 - σ) * Real.sqrt ((𝓢.ν : ℝ) + 1) / σ := sorry

/-- **Lemma 15 (Hessian-norm quadratic contraction).** There exist
absolute constants `ρ* ∈ (0,1)` and `K* ≥ 1` such that one Riemannian
Josephy–Newton step contracts the Hessian-norm proximity as
`δ(u⁺, μ) ≤ K* · δ(u, μ)²` whenever `δ(u, μ) ≤ ρ*`. -/
theorem hessian_quadratic_contraction :
    ∃ ρ_star : ℝ, ∃ K_star : ℝ,
      0 < ρ_star ∧ ρ_star < 1 ∧ 1 ≤ K_star ∧
      ∀ {μ : ℝ}, 0 < μ →
        ∀ {u : H}, u ∈ sphere 𝓢 → u ∈ 𝓢.C →
          delta 𝓢 μ u ≤ ρ_star →
            ∀ {u_next : H} {lam : ℝ}, IsRJNStepA 𝓢 μ u u_next lam →
              delta 𝓢 μ u_next ≤ K_star * (delta 𝓢 μ u) ^ 2 := sorry

/-- **Theorem 16 (Polynomial complexity).** With Hessian-norm
proximity, the path-following scheme
`μ_{k+1} = σ μ_k`, `σ = 1 - α/√(ν+1)`,
followed by `N` corrector steps, maintains `δ(u_k, μ_k) ≤ β`
throughout, with `α, β, N` absolute constants. To reach
`μ_k ≤ ε μ₀` requires at most
`⌈ √(ν+1) / α · log(1/ε) ⌉` outer iterations. -/
theorem polynomial_complexity :
    ∃ α : ℝ, ∃ β : ℝ, ∃ N : ℕ,
      0 < α ∧ α < 1 ∧ 0 < β ∧ β < 1 ∧
      ∀ {μ₀ : ℝ}, 0 < μ₀ →
        ∀ {u₀ : H}, u₀ ∈ sphere 𝓢 → u₀ ∈ 𝓢.C →
          delta 𝓢 μ₀ u₀ ≤ β →
            let σ := 1 - α / Real.sqrt ((𝓢.ν : ℝ) + 1)
            ∃ seq : ℕ → H, seq 0 = u₀ ∧
              ∀ k, seq k ∈ sphere 𝓢 ∩ 𝓢.C ∧
                   delta 𝓢 (σ ^ k * μ₀) (seq k) ≤ β ∧
              ∀ ε : ℝ, 0 < ε →
                ∀ k, k ≥ ⌈Real.sqrt ((𝓢.ν : ℝ) + 1) / α
                          * Real.log (1 / ε)⌉₊ →
                  σ ^ k * μ₀ ≤ ε * μ₀ := sorry

end Irn
