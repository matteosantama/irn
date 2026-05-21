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
import Mathlib.Analysis.InnerProductSpace.ProdL2
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

/-- The ambient Hilbert space of the homogeneous embedding,
`H = X × Y × ℝ` equipped with the `L²` inner product. Implemented as
the nested `WithLp 2 (X × WithLp 2 (Y × ℝ))` so that Mathlib's
`WithLp.instProdInnerProductSpace` chains the inner products
componentwise:
`⟨(xu, yu, τu), (xv, yv, τv)⟩ = ⟨xu, xv⟩_X + ⟨yu, yv⟩_Y + τu·τv`. -/
abbrev H (X Y : Type*)
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] :
    Type _ := WithLp 2 (X × WithLp 2 (Y × ℝ))

variable (𝓟 : ProblemData X Y)

/-- The X-component projection `(x, y, τ) ↦ x`. The `𝓟` argument is
unused — kept so that downstream code can write `𝓟.x_proj u`. -/
def x_proj (_ : ProblemData X Y) (u : H X Y) : X := u.fst

/-- The Y-component projection `(x, y, τ) ↦ y`. -/
def y_proj (_ : ProblemData X Y) (u : H X Y) : Y := u.snd.fst

/-- The τ-component projection `(x, y, τ) ↦ τ`. -/
def tau_proj (_ : ProblemData X Y) (u : H X Y) : ℝ := u.snd.snd

/-- The τ-direction unit vector `(0, 0, 1) ∈ H`. -/
def e_τ (_ : ProblemData X Y) : H X Y :=
  WithLp.toLp 2 ((0 : X), WithLp.toLp 2 ((0 : Y), (1 : ℝ)))

/-- The KKT-feasible cone `C = X × K × ℝ_+`. -/
def C (𝓟 : ProblemData X Y) : Set (H X Y) :=
  {u | 𝓟.y_proj u ∈ 𝓟.K ∧ 0 ≤ 𝓟.tau_proj u}

/-- The relaxed monotonicity domain `C_+ = X × Y × ℝ_++`. -/
def Cplus (𝓟 : ProblemData X Y) : Set (H X Y) :=
  {u | 0 < 𝓟.tau_proj u}

/-- `tau_proj u > 0` on `Cplus` (definitional). -/
theorem tau_proj_pos {u : H X Y} (hu : u ∈ 𝓟.Cplus) :
    0 < 𝓟.tau_proj u := hu

/-- Positive `tau_proj` lands in `Cplus` (definitional). -/
theorem Cplus_of_tau_proj_pos {u : H X Y} (h : 0 < 𝓟.tau_proj u) :
    u ∈ 𝓟.Cplus := h

/-- `⟨u, e_τ⟩ = tau_proj u` — the τ-coordinate is the inner product
with the τ-unit vector. -/
theorem inner_u_e_tau (u : H X Y) :
    inner ℝ u 𝓟.e_τ = 𝓟.tau_proj u := by
  show inner ℝ u
      (WithLp.toLp 2 ((0 : X), WithLp.toLp 2 ((0 : Y), (1 : ℝ)))) = u.snd.snd
  simp [WithLp.prod_inner_apply, inner_zero_right]

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

/-- The block-matrix KKT operator `M : H → H` from the homogeneous
embedding eq. (2.4):
$$ M(x, y, \tau) = \big(\, Px + A^\top y + c\,\tau,\;\; -A x + b\,\tau,
   \;\; -c^\top x - b^\top y \,\big), $$
where `A^\top` is the inner-product adjoint of `A`. The skew off-diagonal
blocks are what makes `⟨u, M u⟩ = ⟨x, P x⟩` (lemma `inner_u_M` below);
the symmetric block `P` is what survives.

Packaged here as a plain function; the `H →L[ℝ] H` linearity packaging
that `IrnSetup` expects can be added later (linearity follows from
each block being a continuous linear map). -/
noncomputable def M_apply (𝓟 : ProblemData X Y) (u : H X Y) : H X Y :=
  WithLp.toLp 2 (
    𝓟.P (𝓟.x_proj u) +
      ContinuousLinearMap.adjoint 𝓟.A (𝓟.y_proj u) +
      𝓟.tau_proj u • 𝓟.c,
    WithLp.toLp 2 (
      -𝓟.A (𝓟.x_proj u) + 𝓟.tau_proj u • 𝓟.b,
      -inner ℝ 𝓟.c (𝓟.x_proj u) - inner ℝ 𝓟.b (𝓟.y_proj u)))

/-- **Euler-type identity for `M`.** `⟨u, M u⟩ = ⟨x, P x⟩`: the skew
off-diagonal blocks cancel pairwise (the `A`/`A†` pair, the `c` pair,
and the `b` pair each contribute zero), leaving only the symmetric
`P`-block. -/
theorem inner_u_M (u : H X Y) :
    inner ℝ u (𝓟.M_apply u) =
      𝓟.Px_bilinform (𝓟.x_proj u) (𝓟.x_proj u) := by
  unfold M_apply Px_bilinform x_proj y_proj tau_proj
  simp only [WithLp.prod_inner_apply, WithLp.fst, WithLp.snd,
             inner_add_right, inner_neg_right, real_inner_smul_right,
             ContinuousLinearMap.adjoint_inner_right,
             RCLike.inner_apply, starRingEnd_apply, star_trivial]
  rw [real_inner_comm (𝓟.A u.ofLp.1) u.ofLp.2.ofLp.1,
      real_inner_comm 𝓟.c u.ofLp.1,
      real_inner_comm 𝓟.b u.ofLp.2.ofLp.1]
  ring

/-- The KKT operator `Q : H → H` from eq. (2.4):
$$ Q(u) = M u - \frac{1}{\tau}\!\big(0,\,0,\,x^\top P x\big)
        = M u - \big(Px_{\mathrm{bilinform}}(x, x) / \tau\big) \cdot e_\tau. $$
Defined only on `Cplus` (the `τ > 0` region) because the rational
correction `Px(x, x)/τ` is undefined at `τ = 0`. The `hu : u ∈ Cplus`
hypothesis is taken explicitly. -/
noncomputable def Q_apply (𝓟 : ProblemData X Y) (u : H X Y)
    (_hu : u ∈ 𝓟.Cplus) : H X Y :=
  𝓟.M_apply u -
    (𝓟.Px_bilinform (𝓟.x_proj u) (𝓟.x_proj u) / 𝓟.tau_proj u) • 𝓟.e_τ

/-- **The `Q_eq` decomposition** — `Q u = M u - (Px(x,x)/τ) • e_τ` — is
the definition itself. -/
theorem Q_eq {u : H X Y} (hu : u ∈ 𝓟.Cplus) :
    𝓟.Q_apply u hu =
      𝓟.M_apply u -
        (𝓟.Px_bilinform (𝓟.x_proj u) (𝓟.x_proj u) / 𝓟.tau_proj u) • 𝓟.e_τ :=
  rfl

/-- **Euler-type identity for `Q`.** `⟨u, Q(u)⟩ = 0` on `Cplus`. The
matrix part contributes `Px(x, x)` (via `inner_u_M`) and the rational
correction contributes `-(Px(x, x)/τ) · τ = -Px(x, x)`, which cancels. -/
theorem inner_u_Q {u : H X Y} (hu : u ∈ 𝓟.Cplus) :
    inner ℝ u (𝓟.Q_apply u hu) = (0 : ℝ) := by
  have hτ : 0 < 𝓟.tau_proj u := 𝓟.tau_proj_pos hu
  have hτ_ne : 𝓟.tau_proj u ≠ 0 := ne_of_gt hτ
  rw [Q_eq hu, inner_sub_right, real_inner_smul_right,
      𝓟.inner_u_M, 𝓟.inner_u_e_tau]
  field_simp
  ring

end ProblemData

end Irn
