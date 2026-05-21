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
import Mathlib.Analysis.Convex.Cone.Basic
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
  /-- The closed pointed convex cone for the dual variable `y`. Mathlib's
  `ProperCone ℝ Y` bundles pointedness (`0 ∈ K`), non-negative scalar
  closure, addition closure, and topological closedness in a single
  type, with `SetLike` providing the natural `y ∈ K` membership. -/
  K : ProperCone ℝ Y
  /-- A `ν`-LHSCB for `K`. -/
  fBarrier : LHSCB Y ν
  /-- The barrier domain is the (topological) interior of `K`. An LHSCB
  is by definition only defined on the interior of its cone, since the
  barrier blows up on the boundary. -/
  fBarrier_domain_eq_interior : fBarrier.domain = interior (K : Set Y)

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

/-- The τ-projection packaged as a continuous linear functional on `H`.
Equals `WithLp.sndL ∘ WithLp.sndL` (taking the second component twice). -/
noncomputable def tau_proj_linear : H X Y →L[ℝ] ℝ :=
  (WithLp.sndL 2 ℝ Y ℝ).comp (WithLp.sndL 2 ℝ X (WithLp 2 (Y × ℝ)))

@[simp] theorem tau_proj_linear_apply (𝓟 : ProblemData X Y) (u : H X Y) :
    tau_proj_linear u = 𝓟.tau_proj u := rfl

/-- The X-projection packaged as a continuous linear map. -/
noncomputable def x_proj_linear : H X Y →L[ℝ] X :=
  WithLp.fstL 2 ℝ X (WithLp 2 (Y × ℝ))

@[simp] theorem x_proj_linear_apply (𝓟 : ProblemData X Y) (u : H X Y) :
    x_proj_linear u = 𝓟.x_proj u := rfl

/-- The Y-projection packaged as a continuous linear map. -/
noncomputable def y_proj_linear : H X Y →L[ℝ] Y :=
  (WithLp.fstL 2 ℝ Y ℝ).comp (WithLp.sndL 2 ℝ X (WithLp 2 (Y × ℝ)))

@[simp] theorem y_proj_linear_apply (𝓟 : ProblemData X Y) (u : H X Y) :
    y_proj_linear u = 𝓟.y_proj u := rfl

/-- The KKT-feasible cone `C = X × K × ℝ_+`. -/
def C (𝓟 : ProblemData X Y) : Set (H X Y) :=
  {u | 𝓟.y_proj u ∈ 𝓟.K ∧ 0 ≤ 𝓟.tau_proj u}

/-- The relaxed monotonicity domain `C_+ = X × Y × ℝ_++`. -/
def Cplus (𝓟 : ProblemData X Y) : Set (H X Y) :=
  {u | 0 < 𝓟.tau_proj u}

/-- The (topological) interior of `C`: `y ∈ int K` and `τ > 0`. This
is where the IRN analysis lives — the barrier `f` is finite here. -/
def C_interior (𝓟 : ProblemData X Y) : Set (H X Y) :=
  {u | 𝓟.y_proj u ∈ interior (𝓟.K : Set Y) ∧ 0 < 𝓟.tau_proj u}

theorem C_interior_subset_C : 𝓟.C_interior ⊆ 𝓟.C := fun _ hu =>
  ⟨interior_subset hu.1, le_of_lt hu.2⟩

theorem C_interior_subset_Cplus : 𝓟.C_interior ⊆ 𝓟.Cplus := fun _ hu => hu.2

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

/-- The primal bilinear form on `H` packaged as a continuous bilinear
map: `Px_bilinform_clm u v = ⟨x_proj u, P (x_proj v)⟩`. Built by
composing `innerSL ℝ` with `x_proj_linear` on both sides (and `P` on
the right). -/
noncomputable def Px_bilinform_clm (𝓟 : ProblemData X Y) :
    H X Y →L[ℝ] H X Y →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp x_proj_linear (𝓟.P.comp x_proj_linear)

@[simp] theorem Px_bilinform_clm_apply (𝓟 : ProblemData X Y) (u v : H X Y) :
    𝓟.Px_bilinform_clm u v = 𝓟.Px_bilinform (𝓟.x_proj u) (𝓟.x_proj v) := rfl

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

/-- The block-matrix KKT operator `M` packaged as a continuous linear
map `H →L[ℝ] H`. Built from the same five pieces as `M_apply`
(`P`, `A`, `A.adjoint`, `b`, `c`) using Mathlib's CLM combinators
(`.comp`, `+`, `.smulRight`, `.prod`, and the WithLp prod equivalence).
The `M_clm_apply` lemma below shows this coincides with `M_apply`. -/
noncomputable def M_clm (𝓟 : ProblemData X Y) :
    H X Y →L[ℝ] H X Y :=
  let x_clm : H X Y →L[ℝ] X := x_proj_linear
  let y_clm : H X Y →L[ℝ] Y := y_proj_linear
  let τ_clm : H X Y →L[ℝ] ℝ := tau_proj_linear
  -- Block 1 (X-output): P x + A† y + τ • c.
  let block1 : H X Y →L[ℝ] X :=
    𝓟.P.comp x_clm + (ContinuousLinearMap.adjoint 𝓟.A).comp y_clm +
      τ_clm.smulRight 𝓟.c
  -- Block 2 (Y-output): -A x + τ • b.
  let block2 : H X Y →L[ℝ] Y :=
    -(𝓟.A.comp x_clm) + τ_clm.smulRight 𝓟.b
  -- Block 3 (ℝ-output): -⟨c, x⟩ - ⟨b, y⟩.
  let block3 : H X Y →L[ℝ] ℝ :=
    -(innerSL ℝ 𝓟.c).comp x_clm - (innerSL ℝ 𝓟.b).comp y_clm
  -- Pair block2 and block3 into (Y × ℝ), then wrap with WithLp.toLp.
  let block23_lp : H X Y →L[ℝ] WithLp 2 (Y × ℝ) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ Y ℝ).symm.toContinuousLinearMap.comp
      (block2.prod block3)
  -- Pair block1 with block23_lp, then wrap.
  (WithLp.prodContinuousLinearEquiv 2 ℝ X (WithLp 2 (Y × ℝ))).symm.toContinuousLinearMap.comp
    (block1.prod block23_lp)

@[simp] theorem M_clm_apply (𝓟 : ProblemData X Y) (u : H X Y) :
    𝓟.M_clm u = 𝓟.M_apply u := rfl

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
  rw [𝓟.Q_eq hu, inner_sub_right, real_inner_smul_right,
      𝓟.inner_u_M, 𝓟.inner_u_e_tau]
  field_simp
  ring

/-- `y_proj` commutes with subtraction (linearity of the projection). -/
lemma y_proj_sub (u v : H X Y) :
    𝓟.y_proj (u - v) = 𝓟.y_proj u - 𝓟.y_proj v := by
  unfold y_proj
  simp

/-- The inner product of `u : H` with a y-block-lifted vector
`(0, yv, 0)` reduces to the inner of the y-component:
`⟨u, (0, yv, 0)⟩_H = ⟨y_proj u, yv⟩_Y`. -/
lemma inner_u_lifted_y (u : H X Y) (yv : Y) :
    inner ℝ u
      (WithLp.toLp 2 ((0 : X), WithLp.toLp 2 (yv, (0 : ℝ)))) =
    inner ℝ (𝓟.y_proj u) yv := by
  unfold y_proj
  simp only [WithLp.prod_inner_apply, inner_zero_right, zero_add, add_zero]
  rfl

/-- The y-projection is continuous (composition of `WithLp.snd` and
`WithLp.fst`). -/
lemma y_proj_continuous : Continuous 𝓟.y_proj := by
  unfold y_proj
  fun_prop

/-- **Lift of `fBarrier` to `H`.** The user's `ν`-LHSCB `f` on `Y` extends
to a `ν`-LHSCB `f_lhscb` on `H = X × Y × ℝ` by acting only on the y-block:
`f_lift(x, y, τ) := f(y)`, with gradient `(0, ∇f(y), 0)`, and domain
`y_proj⁻¹(int K)` (the preimage of the cone interior — open since
`y_proj` is continuous). The Euler identity and gradient monotonicity
transport from `fBarrier`. -/
noncomputable def f_lhscb : LHSCB (H X Y) 𝓟.ν where
  f u := 𝓟.fBarrier.f (𝓟.y_proj u)
  grad u := WithLp.toLp 2 ((0 : X),
    WithLp.toLp 2 (𝓟.fBarrier.grad (𝓟.y_proj u), (0 : ℝ)))
  domain := {u | 𝓟.y_proj u ∈ 𝓟.fBarrier.domain}
  domain_open :=
    𝓟.y_proj_continuous.isOpen_preimage _ 𝓟.fBarrier.domain_open
  euler := by
    intros u hu
    rw [𝓟.inner_u_lifted_y]
    exact 𝓟.fBarrier.euler (𝓟.y_proj u) hu
  grad_monotone := by
    intros u hu v hv
    rw [inner_sub_right, 𝓟.inner_u_lifted_y, 𝓟.inner_u_lifted_y,
        ← inner_sub_right, 𝓟.y_proj_sub]
    exact 𝓟.fBarrier.grad_monotone (𝓟.y_proj u) hu (𝓟.y_proj v) hv

/-- **Totalised `Q`.** A version of `Q_apply` extended to all of `H`
(using Lean's division-by-zero-is-zero convention outside `Cplus`).
Only meaningful on `Cplus`; provided for compatibility with
`IrnSetup.Q : H → H` (which is a total function). -/
noncomputable def Q (𝓟 : ProblemData X Y) (u : H X Y) : H X Y :=
  𝓟.M_apply u -
    (𝓟.Px_bilinform (𝓟.x_proj u) (𝓟.x_proj u) / 𝓟.tau_proj u) • 𝓟.e_τ

/-- `Q` agrees with `Q_apply` on `Cplus` (where Q is mathematically
defined). -/
theorem Q_eq_Q_apply {u : H X Y} (hu : u ∈ 𝓟.Cplus) :
    𝓟.Q u = 𝓟.Q_apply u hu := rfl

/-- **Totalised `φ`.** The barrier-gradient `φ = ∇f + ∇g` lifted to
`H`, where `∇g(u) = (-1/tau_proj u) • e_τ` is the τ-component of the
log barrier's gradient. Total on all of `H` (Lean's
division-by-zero-is-zero convention applies outside `Cplus`). -/
noncomputable def φ (𝓟 : ProblemData X Y) (u : H X Y) : H X Y :=
  𝓟.f_lhscb.grad u + (-1 / 𝓟.tau_proj u) • 𝓟.e_τ

/-- `C_interior` is in the lifted f-barrier domain: if `y_proj u ∈
int K` then `u ∈ f_lhscb.domain`. -/
theorem C_interior_subset_f_lhscb_domain :
    𝓟.C_interior ⊆ 𝓟.f_lhscb.domain := fun u hu => by
  show 𝓟.y_proj u ∈ 𝓟.fBarrier.domain
  rw [𝓟.fBarrier_domain_eq_interior]
  exact hu.1

/-! ### Sphere radius and derived norm facts -/

/-- Sphere radius `r = √(ν+1)`. -/
noncomputable def r : ℝ := Real.sqrt ((𝓟.ν : ℝ) + 1)

theorem r_sq : 𝓟.r ^ 2 = (𝓟.ν : ℝ) + 1 := by
  unfold r
  exact Real.sq_sqrt (by positivity)

theorem r_pos : 0 < 𝓟.r := by
  unfold r
  exact Real.sqrt_pos.mpr (by positivity)

/-! ### `Cplus` topology -/

/-- `Cplus = {u | 0 < tau_proj u}` is open: it's the preimage of
`(0, ∞)` under the continuous linear functional `tau_proj_linear`. -/
theorem Cplus_open : IsOpen 𝓟.Cplus := by
  have h_eq : 𝓟.Cplus =
      (ProblemData.tau_proj_linear : H X Y →L[ℝ] ℝ) ⁻¹' Set.Ioi 0 := by
    ext u
    show 0 < 𝓟.tau_proj u ↔ 0 < tau_proj_linear u
    rw [tau_proj_linear_apply]
  rw [h_eq]
  exact (ProblemData.tau_proj_linear : H X Y →L[ℝ] ℝ).continuous.isOpen_preimage
    _ isOpen_Ioi

/-! ### `Q` monotonicity (Proposition 1) -/

/-- **Proposition 1 (Monotonicity of `Q`).** Direct calculation gives
`⟨u₁ - u₂, Q(u₁) - Q(u₂)⟩ = τ₁τ₂(z₁ - z₂)⊤ P (z₁ - z₂) ≥ 0`. The
τ-rescaling is captured by `Px_quad_form_psd`. -/
theorem Q_monotone (u : H X Y) (hu : u ∈ 𝓟.Cplus)
    (v : H X Y) (hv : v ∈ 𝓟.Cplus) :
    0 ≤ inner ℝ (u - v) (𝓟.Q u - 𝓟.Q v) := by
  have hτu : 0 < 𝓟.tau_proj u := 𝓟.tau_proj_pos hu
  have hτv : 0 < 𝓟.tau_proj v := 𝓟.tau_proj_pos hv
  have hτu_ne : 𝓟.tau_proj u ≠ 0 := ne_of_gt hτu
  have hτv_ne : 𝓟.tau_proj v ≠ 0 := ne_of_gt hτv
  have hτuv : 0 < 𝓟.tau_proj u * 𝓟.tau_proj v := mul_pos hτu hτv
  -- Unfold Q to M_apply minus the rational correction.
  show 0 ≤ inner ℝ (u - v)
    ((𝓟.M_apply u - (𝓟.Px_bilinform (𝓟.x_proj u) (𝓟.x_proj u) /
      𝓟.tau_proj u) • 𝓟.e_τ) -
     (𝓟.M_apply v - (𝓟.Px_bilinform (𝓟.x_proj v) (𝓟.x_proj v) /
      𝓟.tau_proj v) • 𝓟.e_τ))
  -- Use the M_clm packaging to repackage M_apply via M_clm's linearity:
  -- M_apply u - M_apply v = M_clm (u - v) (since M_clm_apply is rfl).
  have h_arrange :
      (𝓟.M_apply u - (𝓟.Px_bilinform (𝓟.x_proj u) (𝓟.x_proj u) /
        𝓟.tau_proj u) • 𝓟.e_τ) -
      (𝓟.M_apply v - (𝓟.Px_bilinform (𝓟.x_proj v) (𝓟.x_proj v) /
        𝓟.tau_proj v) • 𝓟.e_τ) =
      𝓟.M_clm (u - v) -
        ((𝓟.Px_bilinform (𝓟.x_proj u) (𝓟.x_proj u) / 𝓟.tau_proj u) -
          (𝓟.Px_bilinform (𝓟.x_proj v) (𝓟.x_proj v) / 𝓟.tau_proj v)) • 𝓟.e_τ := by
    rw [show 𝓟.M_apply u = 𝓟.M_clm u from rfl,
        show 𝓟.M_apply v = 𝓟.M_clm v from rfl,
        map_sub 𝓟.M_clm]
    module
  rw [h_arrange, inner_sub_right, inner_smul_right]
  -- ⟨u-v, M(u-v)⟩ = Px(x(u-v), x(u-v))
  have h_x_sub : 𝓟.x_proj (u - v) = 𝓟.x_proj u - 𝓟.x_proj v := by
    unfold x_proj
    simp
  have h_inner_M : inner ℝ (u - v) (𝓟.M_clm (u - v)) =
      𝓟.Px_bilinform (𝓟.x_proj u - 𝓟.x_proj v) (𝓟.x_proj u - 𝓟.x_proj v) := by
    rw [show 𝓟.M_clm (u - v) = 𝓟.M_apply (u - v) from rfl, 𝓟.inner_u_M]
    rw [h_x_sub]
  rw [h_inner_M]
  -- Expand `Px(x_u - x_v, x_u - x_v)` bilinearly.
  set xu := 𝓟.x_proj u
  set xv := 𝓟.x_proj v
  have h_Px_expand : 𝓟.Px_bilinform (xu - xv) (xu - xv) =
      𝓟.Px_bilinform xu xu - 2 * 𝓟.Px_bilinform xu xv +
      𝓟.Px_bilinform xv xv := by
    show inner ℝ (xu - xv) (𝓟.P (xu - xv)) =
      inner ℝ xu (𝓟.P xu) - 2 * inner ℝ xu (𝓟.P xv) +
      inner ℝ xv (𝓟.P xv)
    rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right]
    have h_sym : inner ℝ xv (𝓟.P xu) = inner ℝ xu (𝓟.P xv) := by
      rw [← 𝓟.P_symm, real_inner_comm]
    rw [h_sym]
    ring
  rw [h_Px_expand]
  -- `⟨u - v, e_τ⟩ = τ_u - τ_v`.
  have h_inner_etau : inner ℝ (u - v) 𝓟.e_τ = 𝓟.tau_proj u - 𝓟.tau_proj v := by
    rw [inner_sub_left, 𝓟.inner_u_e_tau, 𝓟.inner_u_e_tau]
  rw [h_inner_etau]
  -- Algebraic regrouping into the τ-rescaled PSD form.
  have h_psd :
      0 ≤ 𝓟.tau_proj v ^ 2 * 𝓟.Px_bilinform xu xu -
          2 * 𝓟.tau_proj u * 𝓟.tau_proj v * 𝓟.Px_bilinform xu xv +
          𝓟.tau_proj u ^ 2 * 𝓟.Px_bilinform xv xv :=
    𝓟.Px_quad_form_psd xu xv (𝓟.tau_proj u) (𝓟.tau_proj v)
  have h_id :
      𝓟.Px_bilinform xu xu - 2 * 𝓟.Px_bilinform xu xv +
        𝓟.Px_bilinform xv xv -
          (𝓟.Px_bilinform xu xu / 𝓟.tau_proj u -
            𝓟.Px_bilinform xv xv / 𝓟.tau_proj v) *
              (𝓟.tau_proj u - 𝓟.tau_proj v) =
        (𝓟.tau_proj v ^ 2 * 𝓟.Px_bilinform xu xu -
          2 * 𝓟.tau_proj u * 𝓟.tau_proj v * 𝓟.Px_bilinform xu xv +
          𝓟.tau_proj u ^ 2 * 𝓟.Px_bilinform xv xv) /
          (𝓟.tau_proj u * 𝓟.tau_proj v) := by
    field_simp
    ring
  rw [h_id]
  exact div_nonneg h_psd (le_of_lt hτuv)

/-! ### The combined `(ν+1)`-LHSCB `F = f + g` -/

/-- The concrete `1`-LHSCB `g(τ) = -log τ` lifted to `H`. The gradient
is `(-1/tau_proj u) • e_τ`; Euler uses `inner_u_e_tau`; monotonicity
uses `(τ_u - τ_v)² / (τ_u τ_v) ≥ 0`. -/
noncomputable def g_lhscb : LHSCB (H X Y) 1 where
  f := fun u => -Real.log (𝓟.tau_proj u)
  grad := fun u => (-1 / 𝓟.tau_proj u) • 𝓟.e_τ
  domain := 𝓟.Cplus
  domain_open := 𝓟.Cplus_open
  euler := by
    intros u hu
    have hτ : 0 < 𝓟.tau_proj u := 𝓟.tau_proj_pos hu
    have hτ_ne : 𝓟.tau_proj u ≠ 0 := ne_of_gt hτ
    rw [inner_smul_right, 𝓟.inner_u_e_tau]
    push_cast
    field_simp
  grad_monotone := by
    intros u hu v hv
    have hτu : 0 < 𝓟.tau_proj u := 𝓟.tau_proj_pos hu
    have hτv : 0 < 𝓟.tau_proj v := 𝓟.tau_proj_pos hv
    have hτu_ne : 𝓟.tau_proj u ≠ 0 := ne_of_gt hτu
    have hτv_ne : 𝓟.tau_proj v ≠ 0 := ne_of_gt hτv
    have h_sub_smul :
        (-1 / 𝓟.tau_proj u) • 𝓟.e_τ - (-1 / 𝓟.tau_proj v) • 𝓟.e_τ =
        ((-1 / 𝓟.tau_proj u) - (-1 / 𝓟.tau_proj v)) • 𝓟.e_τ := by
      rw [sub_smul]
    rw [h_sub_smul, inner_smul_right]
    have h_inner :
        inner ℝ (u - v) 𝓟.e_τ = 𝓟.tau_proj u - 𝓟.tau_proj v := by
      rw [inner_sub_left, 𝓟.inner_u_e_tau, 𝓟.inner_u_e_tau]
    rw [h_inner]
    have h_factor :
        ((-1 / 𝓟.tau_proj u) - (-1 / 𝓟.tau_proj v)) *
            (𝓟.tau_proj u - 𝓟.tau_proj v) =
        (𝓟.tau_proj u - 𝓟.tau_proj v) ^ 2 /
            (𝓟.tau_proj u * 𝓟.tau_proj v) := by
      field_simp
      ring
    rw [h_factor]
    positivity

/-- The combined `(ν+1)`-LHSCB `F = f + g` driving the IRN central path. -/
noncomputable def F_lhscb : LHSCB (H X Y) (𝓟.ν + 1) :=
  𝓟.f_lhscb.add 𝓟.g_lhscb

/-- `C_interior ⊆ F_lhscb.domain = f_lhscb.domain ∩ Cplus`. -/
theorem C_interior_subset_F_domain : 𝓟.C_interior ⊆ 𝓟.F_lhscb.domain :=
  fun _ hu =>
    ⟨𝓟.C_interior_subset_f_lhscb_domain hu, 𝓟.C_interior_subset_Cplus hu⟩

/-- The IRN setup's `φ` equals the combined LHSCB gradient on
`C_interior`. -/
theorem phi_eq_F_grad (u : H X Y) (_hu : u ∈ 𝓟.C_interior) :
    𝓟.φ u = 𝓟.F_lhscb.grad u := by
  show 𝓟.φ u = (𝓟.f_lhscb.add 𝓟.g_lhscb).grad u
  rw [LHSCB.add_grad]
  rfl

/-- **Euler-type identity for `φ`** (Proposition 3):
`⟨u, φ(u)⟩ = -(ν+1)` on `C_interior`. -/
theorem inner_u_phi (u : H X Y) (hu : u ∈ 𝓟.C_interior) :
    inner ℝ u (𝓟.φ u) = -((𝓟.ν : ℝ) + 1) := by
  rw [𝓟.phi_eq_F_grad u hu,
    𝓟.F_lhscb.euler u (𝓟.C_interior_subset_F_domain hu)]
  push_cast
  ring

/-- **Monotonicity of `φ`** on `C_interior`. The gradient of a convex
function is monotone; here `F = f + g` is convex. -/
theorem phi_monotone (u : H X Y) (hu : u ∈ 𝓟.C_interior)
    (v : H X Y) (hv : v ∈ 𝓟.C_interior) :
    0 ≤ inner ℝ (u - v) (𝓟.φ u - 𝓟.φ v) := by
  rw [𝓟.phi_eq_F_grad u hu, 𝓟.phi_eq_F_grad v hv]
  exact 𝓟.F_lhscb.grad_monotone u (𝓟.C_interior_subset_F_domain hu) v
    (𝓟.C_interior_subset_F_domain hv)

end ProblemData

end Irn
