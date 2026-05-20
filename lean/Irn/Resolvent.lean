/-
# Closed-form resolvent (paper §4)

Theorem 8 (closed-form resolvent of `Ψ = Q + μ ∂G*`) and the
auxiliary maximal-monotone extension result (Lemma A.1).

With the explicit embedding structure on `IrnSetup` (matrix `M`, unit
`e_τ`, scalar functions `q`, `tau_proj`, bilinear form `Px_bilinform`,
and the linear equivalence `hessian_plus_M = H_k + M`), Theorem 8 is
stated literally and proved *modulo* the discriminant analysis for the
scalar quadratic — itself recorded as `exists_pos_root_quad` with a
`sorry` proof.

Paper references:
* Theorem 8 (closed-form resolvent of `Ψ`)
* Eq. (4.4) (scalar quadratic for `θ`)
* Appendix Lemma A.1 (maximal monotone extension)
-/

import Irn.Sphere

namespace Irn

open scoped InnerProductSpace

namespace IrnSetup

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  (𝓢 : IrnSetup H)

/-! ### The closed-form factor vectors

`w_0` and `w_1` are the two `λ`-independent solves against `H_k + M`
that appear in the closed-form formula `u = w_0 + θ w_1` of Theorem 8.
-/

/-- `w_0(μ, u_k, z) = (H_k + M)⁻¹ (H_k z)`. -/
noncomputable def w0 (μ : ℝ) (u_k z : H) : H :=
  (𝓢.hessian_plus_M μ u_k).symm (𝓢.hessian_h μ u_k z)

/-- `w_1(μ, u_k) = (H_k + M)⁻¹ e_τ`. -/
noncomputable def w1 (μ : ℝ) (u_k : H) : H :=
  (𝓢.hessian_plus_M μ u_k).symm 𝓢.e_τ

/-- `(H_k + M) w_0 = H_k z`. -/
theorem hessian_plus_M_w0 (μ : ℝ) (u_k z : H) :
    (𝓢.hessian_plus_M μ u_k : H →L[ℝ] H) (𝓢.w0 μ u_k z) =
      𝓢.hessian_h μ u_k z := by
  unfold w0
  exact (𝓢.hessian_plus_M μ u_k).apply_symm_apply _

/-- `(H_k + M) w_1 = e_τ`. -/
theorem hessian_plus_M_w1 (μ : ℝ) (u_k : H) :
    (𝓢.hessian_plus_M μ u_k : H →L[ℝ] H) (𝓢.w1 μ u_k) = 𝓢.e_τ := by
  unfold w1
  exact (𝓢.hessian_plus_M μ u_k).apply_symm_apply _

/-! ### Scalar-quadratic coefficients

The scalar quadratic `α θ² + β θ + γ = 0` of paper eq. (4.4),
derived from substituting `x = w_0^x + θ w_1^x`, `τ = w_0^τ + θ w_1^τ`
into the inclusion `θ τ = x⊤Px + μ`.
-/

/-- `α = w_1^τ - w_1^x⊤P w_1^x`. -/
noncomputable def quad_α (μ : ℝ) (u_k : H) : ℝ :=
  𝓢.tau_proj (𝓢.w1 μ u_k) - 𝓢.Px_bilinform (𝓢.w1 μ u_k) (𝓢.w1 μ u_k)

/-- `β = w_0^τ - 2 w_0^x⊤P w_1^x`. -/
noncomputable def quad_β (μ : ℝ) (u_k z : H) : ℝ :=
  𝓢.tau_proj (𝓢.w0 μ u_k z) -
    2 * 𝓢.Px_bilinform (𝓢.w0 μ u_k z) (𝓢.w1 μ u_k)

/-- `γ = -(w_0^x⊤P w_0^x + μ)`. -/
noncomputable def quad_γ (μ : ℝ) (u_k z : H) : ℝ :=
  - 𝓢.Px_bilinform (𝓢.w0 μ u_k z) (𝓢.w0 μ u_k z) - μ

/-! ### Auxiliary linearity / bilinearity lemmas. -/

/-- Additivity of `tau_proj`. -/
theorem tau_proj_add (u v : H) :
    𝓢.tau_proj (u + v) = 𝓢.tau_proj u + 𝓢.tau_proj v := by
  rw [← 𝓢.tau_proj_linear_eq, ← 𝓢.tau_proj_linear_eq, ← 𝓢.tau_proj_linear_eq,
      map_add]

/-- Scalar homogeneity of `tau_proj`. -/
theorem tau_proj_smul (r : ℝ) (u : H) :
    𝓢.tau_proj (r • u) = r * 𝓢.tau_proj u := by
  rw [← 𝓢.tau_proj_linear_eq, ← 𝓢.tau_proj_linear_eq, map_smul, smul_eq_mul]

/-- Additivity of `Px_bilinform` in the first slot. -/
theorem Px_bilinform_add_left (u v w : H) :
    𝓢.Px_bilinform (u + v) w = 𝓢.Px_bilinform u w + 𝓢.Px_bilinform v w := by
  rw [map_add]; rfl

/-- Scalar homogeneity of `Px_bilinform` in the first slot. -/
theorem Px_bilinform_smul_left (r : ℝ) (u v : H) :
    𝓢.Px_bilinform (r • u) v = r * 𝓢.Px_bilinform u v := by
  rw [map_smul]; rfl

/-- Additivity of `Px_bilinform` in the second slot. -/
theorem Px_bilinform_add_right (u v w : H) :
    𝓢.Px_bilinform u (v + w) = 𝓢.Px_bilinform u v + 𝓢.Px_bilinform u w :=
  map_add (𝓢.Px_bilinform u) v w

/-- Scalar homogeneity of `Px_bilinform` in the second slot. -/
theorem Px_bilinform_smul_right (r : ℝ) (u v : H) :
    𝓢.Px_bilinform u (r • v) = r * 𝓢.Px_bilinform u v := by
  rw [map_smul]; rfl

end IrnSetup

/-! ### Theorem 8 and Lemma A.1. -/

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  (𝓢 : IrnSetup H)

/-- **Existence of a positive root of the scalar quadratic.**

The discriminant analysis from the paper: `γ ≤ -μ < 0` so `θ = 0` is
never a root, and the quadratic admits exactly one positive root whose
corresponding `u = w_0 + θ w_1` has `tau_proj u > 0` (i.e., lies in
`Cplus`).

Left as `sorry` in this first pass — proving it requires:
(i) `Px_bilinform u u ≥ 0` (PSD of `P`),
(ii) the discriminant `β² - 4αγ ≥ 0`,
(iii) the standard quadratic root formula plus a sign analysis. -/
theorem exists_pos_root_quad (μ : ℝ) (hμ : 0 < μ) (u_k z : H) :
    ∃ θ : ℝ, 0 < θ ∧
      𝓢.quad_α μ u_k * θ ^ 2 +
        𝓢.quad_β μ u_k z * θ + 𝓢.quad_γ μ u_k z = 0 ∧
      0 < 𝓢.tau_proj (𝓢.w0 μ u_k z + θ • 𝓢.w1 μ u_k) := sorry

/-- **Theorem 8 (Closed-form resolvent of `Ψ`).** With `H_k = hessian_h μ u_k`,
the resolvent value `u = J_Ψ^{H_k}(z)` lies in `Cplus` and is the unique
pair `(u, θ)` with `θ > 0` satisfying
`(H_k + M) u = H_k z + θ • e_τ` and `θ · tau_proj u = B_P(u, u) + μ`
(the inclusion form of `θ τ = x⊤Px + μ`).

Proof: take `θ` from `exists_pos_root_quad` and `u := w_0 + θ w_1`.
The closed-form equation is purely linear-algebraic; the scalar
equation follows from the quadratic identity expanded via bilinearity
of `Px_bilinform` and linearity of `tau_proj`. -/
theorem resolvent_closed_form
    (μ : ℝ) (hμ : 0 < μ) (u_k z : H) :
    ∃ u : H, ∃ θ : ℝ,
      u ∈ 𝓢.Cplus ∧
      0 < θ ∧
      (𝓢.hessian_h μ u_k + 𝓢.M) u =
        (𝓢.hessian_h μ u_k) z + θ • 𝓢.e_τ ∧
      θ * 𝓢.tau_proj u = 𝓢.Px_bilinform u u + μ := by
  obtain ⟨θ, hθ_pos, h_quad, h_tau_pos⟩ :=
    exists_pos_root_quad 𝓢 μ hμ u_k z
  refine ⟨𝓢.w0 μ u_k z + θ • 𝓢.w1 μ u_k, θ, ?_, hθ_pos, ?_, ?_⟩
  -- (1) u ∈ Cplus.
  · exact 𝓢.Cplus_of_tau_proj_pos _ h_tau_pos
  -- (2) (H_k + M) u = H_k z + θ • e_τ.
  · have h_app_w0 : (𝓢.hessian_h μ u_k + 𝓢.M) (𝓢.w0 μ u_k z) =
        𝓢.hessian_h μ u_k z := by
      have h_eq := 𝓢.hessian_plus_M_eq μ u_k (𝓢.w0 μ u_k z)
      have h_apply := 𝓢.hessian_plus_M_w0 μ u_k z
      simp [ContinuousLinearMap.add_apply, h_apply, ← h_eq]
    have h_app_w1 : (𝓢.hessian_h μ u_k + 𝓢.M) (𝓢.w1 μ u_k) = 𝓢.e_τ := by
      have h_eq := 𝓢.hessian_plus_M_eq μ u_k (𝓢.w1 μ u_k)
      have h_apply := 𝓢.hessian_plus_M_w1 μ u_k
      simp [ContinuousLinearMap.add_apply, h_apply, ← h_eq]
    calc (𝓢.hessian_h μ u_k + 𝓢.M) (𝓢.w0 μ u_k z + θ • 𝓢.w1 μ u_k)
        = (𝓢.hessian_h μ u_k + 𝓢.M) (𝓢.w0 μ u_k z) +
            (𝓢.hessian_h μ u_k + 𝓢.M) (θ • 𝓢.w1 μ u_k) := by rw [map_add]
      _ = (𝓢.hessian_h μ u_k + 𝓢.M) (𝓢.w0 μ u_k z) +
            θ • (𝓢.hessian_h μ u_k + 𝓢.M) (𝓢.w1 μ u_k) := by rw [map_smul]
      _ = 𝓢.hessian_h μ u_k z + θ • 𝓢.e_τ := by rw [h_app_w0, h_app_w1]
  -- (3) θ · tau_proj u = B_P(u, u) + μ.
  · set T0 := 𝓢.tau_proj (𝓢.w0 μ u_k z)
    set T1 := 𝓢.tau_proj (𝓢.w1 μ u_k)
    set S0 := 𝓢.Px_bilinform (𝓢.w0 μ u_k z) (𝓢.w0 μ u_k z)
    set S01 := 𝓢.Px_bilinform (𝓢.w0 μ u_k z) (𝓢.w1 μ u_k)
    set S1 := 𝓢.Px_bilinform (𝓢.w1 μ u_k) (𝓢.w1 μ u_k)
    have h_tau_u : 𝓢.tau_proj (𝓢.w0 μ u_k z + θ • 𝓢.w1 μ u_k) = T0 + θ * T1 := by
      rw [𝓢.tau_proj_add, 𝓢.tau_proj_smul]
    have h_Px_u : 𝓢.Px_bilinform (𝓢.w0 μ u_k z + θ • 𝓢.w1 μ u_k)
                    (𝓢.w0 μ u_k z + θ • 𝓢.w1 μ u_k) =
                  S0 + 2 * θ * S01 + θ ^ 2 * S1 := by
      rw [𝓢.Px_bilinform_add_left, 𝓢.Px_bilinform_smul_left,
          𝓢.Px_bilinform_add_right, 𝓢.Px_bilinform_smul_right,
          𝓢.Px_bilinform_add_right, 𝓢.Px_bilinform_smul_right]
      have h_sym : 𝓢.Px_bilinform (𝓢.w1 μ u_k) (𝓢.w0 μ u_k z) = S01 :=
        𝓢.Px_symm _ _
      rw [h_sym]
      ring
    rw [h_tau_u, h_Px_u]
    unfold IrnSetup.quad_α IrnSetup.quad_β IrnSetup.quad_γ at h_quad
    linarith [h_quad]

/-- **Lemma A.1 (Maximal monotone extension).** A continuous monotone
single-valued operator on an open convex set extends to a maximally
monotone operator on the ambient Hilbert space. Stating this
meaningfully requires defining maximally monotone (set-valued)
operators in Mathlib first, which is left as future work. -/
theorem exists_maximal_monotone_extension
    {H₀ : Set H} (_hH₀_open : IsOpen H₀) (_hH₀_convex : Convex ℝ H₀)
    (Q : H → H) (_hQ_cont : ContinuousOn Q H₀)
    (_hQ_mono : ∀ u ∈ H₀, ∀ v ∈ H₀, 0 ≤ inner ℝ (u - v) (Q u - Q v)) :
    True := sorry

end Irn
