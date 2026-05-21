/-
# Problem data (paper §1, §2.1)

The fundamental data of a conic quadratic program:

* a **symmetric PSD** quadratic operator `P : X →L[ℝ] X`,
* a linear constraint operator `A : X →L[ℝ] Y` with right-hand side `b ∈ Y`,
* a primal cost vector `c ∈ X`,
* a closed pointed convex cone `K ⊆ Y` with a `ν`-LHSCB `fBarrier`.

This commit introduces the `ProblemData` structure and proves
elementary `P`-side facts (`Px_bilinform_symm`, `Px_quad_form_psd`)
that follow immediately from `P`'s symmetry and positive semidefiniteness.

Subsequent commits build the homogeneous embedding ambient space
`H = X × Y × ℝ` (with the `L²` inner product via `WithLp 2`), the
KKT operator `Q`, the barrier-gradient map `φ`, and finally a
`toIrnSetup` constructor that bridges to the existing analysis pipeline.

Paper references:
* Eq. (1.1)–(1.2) — primal/dual conic QP
* §2.2, eq. (2.4) — KKT operator `Q`
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Irn.Barriers

namespace Irn

open scoped InnerProductSpace

/-- The fundamental problem data for a conic quadratic program:
$$\min \tfrac{1}{2}\,x^\top P x + c^\top x \quad
  \text{s.t.}\;\; A x + s = b,\;\; s \in \K^{*},\;\; y \in \K,$$
where the only inputs are:

* a **symmetric PSD** operator `P : X →L[ℝ] X`,
* a linear operator `A : X →L[ℝ] Y` and a right-hand side `b ∈ Y`,
* a primal cost vector `c ∈ X`,
* a **closed pointed convex cone** `K ⊆ Y` with a `ν`-LHSCB `fBarrier`.

`X` and `Y` are finite-dimensional real inner-product spaces (the paper
takes `X = ℝⁿ`, `Y = ℝᵐ`). The cone `K` is the cone where the dual
variable `y` lives. -/
structure ProblemData (X : Type*) (Y : Type*)
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    where
  /-- The PSD primal quadratic operator. -/
  P : X →L[ℝ] X
  /-- `P` is symmetric. -/
  P_symm : ∀ x x' : X, inner ℝ (P x) x' = inner ℝ x (P x')
  /-- `P` is positive semidefinite. -/
  P_psd : ∀ x : X, 0 ≤ inner ℝ x (P x)
  /-- The linear constraint operator. -/
  A : X →L[ℝ] Y
  /-- The constraint right-hand side. -/
  b : Y
  /-- The primal cost vector. -/
  c : X
  /-- LHSCB barrier parameter. -/
  ν : ℕ
  ν_pos : 0 < ν
  /-- The cone for the dual variable `y` (closed, pointed, convex). -/
  K : Set Y
  /-- `0 ∈ K` (pointedness). -/
  K_zero_mem : (0 : Y) ∈ K
  /-- Closed under non-negative scalar multiplication. -/
  K_smul_mem : ∀ r : ℝ, 0 ≤ r → ∀ y ∈ K, r • y ∈ K
  /-- Closed under addition (with `K_smul_mem` this gives convexity). -/
  K_add_mem : ∀ y₁ ∈ K, ∀ y₂ ∈ K, y₁ + y₂ ∈ K
  /-- Topologically closed. -/
  K_closed : IsClosed K
  /-- A `ν`-LHSCB for `K`. -/
  fBarrier : LHSCB Y ν
  /-- The barrier domain is contained in `K`. -/
  fBarrier_domain_subset : fBarrier.domain ⊆ K

namespace ProblemData

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  (𝓟 : ProblemData X Y)

/-- The primal bilinear form `B_P(x, x') = ⟨x, P x'⟩` from the quadratic. -/
def Px_bilinform (x x' : X) : ℝ := inner ℝ x (𝓟.P x')

/-- `Px_bilinform` is symmetric (because `P` is symmetric). -/
theorem Px_bilinform_symm (x x' : X) :
    𝓟.Px_bilinform x x' = 𝓟.Px_bilinform x' x := by
  unfold Px_bilinform
  rw [← 𝓟.P_symm, real_inner_comm]

/-- `Px_bilinform` is non-negative on the diagonal (because `P` is PSD). -/
theorem Px_bilinform_self_nonneg (x : X) :
    0 ≤ 𝓟.Px_bilinform x x :=
  𝓟.P_psd x

/-- **τ-rescaled PSD form**:
`τ_v² Px(x_u, x_u) − 2 τ_u τ_v Px(x_u, x_v) + τ_u² Px(x_v, x_v) ≥ 0`.
Equal to `⟨τ_v x_u − τ_u x_v, P (τ_v x_u − τ_u x_v)⟩`, which is `≥ 0`
by `P_psd`. This is the algebraic core of the monotonicity of `Q` (in
the homogeneous embedding, with `τ_u, τ_v` interpreted as
`tau_proj u`, `tau_proj v`). -/
theorem Px_quad_form_psd (xu xv : X) (τu τv : ℝ) :
    0 ≤ τv ^ 2 * 𝓟.Px_bilinform xu xu
        - 2 * τu * τv * 𝓟.Px_bilinform xu xv
        + τu ^ 2 * 𝓟.Px_bilinform xv xv := by
  have h_psd : 0 ≤ inner ℝ (τv • xu - τu • xv) (𝓟.P (τv • xu - τu • xv)) :=
    𝓟.P_psd _
  have h_sym : inner ℝ xv (𝓟.P xu) = inner ℝ xu (𝓟.P xv) := by
    rw [← 𝓟.P_symm, real_inner_comm]
  have h_expand :
      inner ℝ (τv • xu - τu • xv) (𝓟.P (τv • xu - τu • xv)) =
      τv ^ 2 * 𝓟.Px_bilinform xu xu
        - 2 * τu * τv * 𝓟.Px_bilinform xu xv
        + τu ^ 2 * 𝓟.Px_bilinform xv xv := by
    show inner ℝ (τv • xu - τu • xv) (𝓟.P (τv • xu - τu • xv)) =
        τv ^ 2 * inner ℝ xu (𝓟.P xu)
          - 2 * τu * τv * inner ℝ xu (𝓟.P xv)
          + τu ^ 2 * inner ℝ xv (𝓟.P xv)
    rw [map_sub, ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul,
        inner_sub_left, inner_sub_right, inner_sub_right,
        real_inner_smul_left, real_inner_smul_left,
        real_inner_smul_left, real_inner_smul_left,
        real_inner_smul_right, real_inner_smul_right,
        real_inner_smul_right, real_inner_smul_right,
        h_sym]
    ring
  linarith [h_psd, h_expand]

end ProblemData

end Irn
