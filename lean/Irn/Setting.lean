/-
# Problem data (paper §1, §2.1)

The fundamental data of a conic quadratic program:

* a **symmetric PSD** quadratic operator `P : X →L[ℝ] X`,
* a linear constraint operator `A : X →L[ℝ] Y` with right-hand side `b ∈ Y`,
* a primal cost vector `c ∈ X`,
* a closed pointed convex cone `K ⊆ Y` with a `ν`-LHSCB `fBarrier`.

This commit introduces the `IrnSetup` structure and proves
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
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
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
structure IrnSetup (X : Type*) (Y : Type*)
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
  /-- A `ν`-LHSCB for the cone `K`. The barrier is finite on
  `interior (K : Set Y)`. -/
  fBarrier : LHSCB Y (K : Set Y) ν

namespace IrnSetup

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

variable (𝓢 : IrnSetup X Y)

/-- The X-component projection `(x, y, τ) ↦ x`. The `𝓢` argument is
unused — kept so that downstream code can write `𝓢.x_proj u`. -/
def x_proj (_ : IrnSetup X Y) (u : H X Y) : X := u.fst

/-- The Y-component projection `(x, y, τ) ↦ y`. -/
def y_proj (_ : IrnSetup X Y) (u : H X Y) : Y := u.snd.fst

/-- The τ-component projection `(x, y, τ) ↦ τ`. -/
def tau_proj (_ : IrnSetup X Y) (u : H X Y) : ℝ := u.snd.snd

/-- The τ-direction unit vector `(0, 0, 1) ∈ H`. -/
def e_τ (_ : IrnSetup X Y) : H X Y :=
  WithLp.toLp 2 ((0 : X), WithLp.toLp 2 ((0 : Y), (1 : ℝ)))

/-- The τ-projection packaged as a continuous linear functional on `H`.
Equals `WithLp.sndL ∘ WithLp.sndL` (taking the second component twice). -/
noncomputable def tau_proj_linear : H X Y →L[ℝ] ℝ :=
  (WithLp.sndL 2 ℝ Y ℝ).comp (WithLp.sndL 2 ℝ X (WithLp 2 (Y × ℝ)))

@[simp] theorem tau_proj_linear_apply (𝓢 : IrnSetup X Y) (u : H X Y) :
    tau_proj_linear u = 𝓢.tau_proj u := rfl

/-- The X-projection packaged as a continuous linear map. -/
noncomputable def x_proj_linear : H X Y →L[ℝ] X :=
  WithLp.fstL 2 ℝ X (WithLp 2 (Y × ℝ))

@[simp] theorem x_proj_linear_apply (𝓢 : IrnSetup X Y) (u : H X Y) :
    x_proj_linear u = 𝓢.x_proj u := rfl

/-- The Y-projection packaged as a continuous linear map. -/
noncomputable def y_proj_linear : H X Y →L[ℝ] Y :=
  (WithLp.fstL 2 ℝ Y ℝ).comp (WithLp.sndL 2 ℝ X (WithLp 2 (Y × ℝ)))

@[simp] theorem y_proj_linear_apply (𝓢 : IrnSetup X Y) (u : H X Y) :
    y_proj_linear u = 𝓢.y_proj u := rfl

/-- The KKT-feasible cone `C = X × K × ℝ_+`. -/
def C (𝓢 : IrnSetup X Y) : Set (H X Y) :=
  {u | 𝓢.y_proj u ∈ 𝓢.K ∧ 0 ≤ 𝓢.tau_proj u}

/-- The relaxed monotonicity domain `C_+ = X × Y × ℝ_++`. -/
def Cplus (𝓢 : IrnSetup X Y) : Set (H X Y) :=
  {u | 0 < 𝓢.tau_proj u}

/-- The (topological) interior of `C`: `y ∈ int K` and `τ > 0`. This
is where the IRN analysis lives — the barrier `f` is finite here. -/
def C_interior (𝓢 : IrnSetup X Y) : Set (H X Y) :=
  {u | 𝓢.y_proj u ∈ interior (𝓢.K : Set Y) ∧ 0 < 𝓢.tau_proj u}

theorem C_interior_subset_C : 𝓢.C_interior ⊆ 𝓢.C := fun _ hu =>
  ⟨interior_subset hu.1, le_of_lt hu.2⟩

theorem C_interior_subset_Cplus : 𝓢.C_interior ⊆ 𝓢.Cplus := fun _ hu => hu.2

/-- `tau_proj u > 0` on `Cplus` (definitional). -/
theorem tau_proj_pos {u : H X Y} (hu : u ∈ 𝓢.Cplus) :
    0 < 𝓢.tau_proj u := hu

/-- Positive `tau_proj` lands in `Cplus` (definitional). -/
theorem Cplus_of_tau_proj_pos {u : H X Y} (h : 0 < 𝓢.tau_proj u) :
    u ∈ 𝓢.Cplus := h

/-- `⟨u, e_τ⟩ = tau_proj u` — the τ-coordinate is the inner product
with the τ-unit vector. -/
theorem inner_u_e_tau (u : H X Y) :
    inner ℝ u 𝓢.e_τ = 𝓢.tau_proj u := by
  show inner ℝ u
      (WithLp.toLp 2 ((0 : X), WithLp.toLp 2 ((0 : Y), (1 : ℝ)))) = u.snd.snd
  simp [WithLp.prod_inner_apply, inner_zero_right]

/-- The primal bilinear form `B_P(x, x') = ⟨x, P x'⟩` from the quadratic. -/
def Px_bilinform (x x' : X) : ℝ := inner ℝ x (𝓢.P x')

/-- `Px_bilinform` is symmetric (because `P` is symmetric). -/
theorem Px_bilinform_symm (x x' : X) :
    𝓢.Px_bilinform x x' = 𝓢.Px_bilinform x' x := by
  unfold Px_bilinform
  rw [← 𝓢.P_symm, real_inner_comm]

/-- `Px_bilinform` is non-negative on the diagonal (because `P` is PSD). -/
theorem Px_bilinform_self_nonneg (x : X) :
    0 ≤ 𝓢.Px_bilinform x x :=
  𝓢.P_psd x

/-- **τ-rescaled PSD form**:
`τ_v² Px(x_u, x_u) − 2 τ_u τ_v Px(x_u, x_v) + τ_u² Px(x_v, x_v) ≥ 0`.
Equal to `⟨τ_v x_u − τ_u x_v, P (τ_v x_u − τ_u x_v)⟩`, which is `≥ 0`
by `P_psd`. This is the algebraic core of the monotonicity of `Q` (in
the homogeneous embedding, with `τ_u, τ_v` interpreted as
`tau_proj u`, `tau_proj v`). -/
theorem Px_quad_form_psd (xu xv : X) (τu τv : ℝ) :
    0 ≤ τv ^ 2 * 𝓢.Px_bilinform xu xu
        - 2 * τu * τv * 𝓢.Px_bilinform xu xv
        + τu ^ 2 * 𝓢.Px_bilinform xv xv := by
  have h_psd : 0 ≤ inner ℝ (τv • xu - τu • xv) (𝓢.P (τv • xu - τu • xv)) :=
    𝓢.P_psd _
  have h_sym : inner ℝ xv (𝓢.P xu) = inner ℝ xu (𝓢.P xv) := by
    rw [← 𝓢.P_symm, real_inner_comm]
  have h_expand :
      inner ℝ (τv • xu - τu • xv) (𝓢.P (τv • xu - τu • xv)) =
      τv ^ 2 * 𝓢.Px_bilinform xu xu
        - 2 * τu * τv * 𝓢.Px_bilinform xu xv
        + τu ^ 2 * 𝓢.Px_bilinform xv xv := by
    show inner ℝ (τv • xu - τu • xv) (𝓢.P (τv • xu - τu • xv)) =
        τv ^ 2 * inner ℝ xu (𝓢.P xu)
          - 2 * τu * τv * inner ℝ xu (𝓢.P xv)
          + τu ^ 2 * inner ℝ xv (𝓢.P xv)
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
noncomputable def Px_bilinform_clm (𝓢 : IrnSetup X Y) :
    H X Y →L[ℝ] H X Y →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp x_proj_linear (𝓢.P.comp x_proj_linear)

@[simp] theorem Px_bilinform_clm_apply (𝓢 : IrnSetup X Y) (u v : H X Y) :
    𝓢.Px_bilinform_clm u v = 𝓢.Px_bilinform (𝓢.x_proj u) (𝓢.x_proj v) := rfl

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
noncomputable def M_apply (𝓢 : IrnSetup X Y) (u : H X Y) : H X Y :=
  WithLp.toLp 2 (
    𝓢.P (𝓢.x_proj u) +
      ContinuousLinearMap.adjoint 𝓢.A (𝓢.y_proj u) +
      𝓢.tau_proj u • 𝓢.c,
    WithLp.toLp 2 (
      -𝓢.A (𝓢.x_proj u) + 𝓢.tau_proj u • 𝓢.b,
      -inner ℝ 𝓢.c (𝓢.x_proj u) - inner ℝ 𝓢.b (𝓢.y_proj u)))

/-- The block-matrix KKT operator `M` packaged as a continuous linear
map `H →L[ℝ] H`. Built from the same five pieces as `M_apply`
(`P`, `A`, `A.adjoint`, `b`, `c`) using Mathlib's CLM combinators
(`.comp`, `+`, `.smulRight`, `.prod`, and the WithLp prod equivalence).
The `M_clm_apply` lemma below shows this coincides with `M_apply`. -/
noncomputable def M_clm (𝓢 : IrnSetup X Y) :
    H X Y →L[ℝ] H X Y :=
  let x_clm : H X Y →L[ℝ] X := x_proj_linear
  let y_clm : H X Y →L[ℝ] Y := y_proj_linear
  let τ_clm : H X Y →L[ℝ] ℝ := tau_proj_linear
  -- Block 1 (X-output): P x + A† y + τ • c.
  let block1 : H X Y →L[ℝ] X :=
    𝓢.P.comp x_clm + (ContinuousLinearMap.adjoint 𝓢.A).comp y_clm +
      τ_clm.smulRight 𝓢.c
  -- Block 2 (Y-output): -A x + τ • b.
  let block2 : H X Y →L[ℝ] Y :=
    -(𝓢.A.comp x_clm) + τ_clm.smulRight 𝓢.b
  -- Block 3 (ℝ-output): -⟨c, x⟩ - ⟨b, y⟩.
  let block3 : H X Y →L[ℝ] ℝ :=
    -(innerSL ℝ 𝓢.c).comp x_clm - (innerSL ℝ 𝓢.b).comp y_clm
  -- Pair block2 and block3 into (Y × ℝ), then wrap with WithLp.toLp.
  let block23_lp : H X Y →L[ℝ] WithLp 2 (Y × ℝ) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ Y ℝ).symm.toContinuousLinearMap.comp
      (block2.prod block3)
  -- Pair block1 with block23_lp, then wrap.
  (WithLp.prodContinuousLinearEquiv 2 ℝ X (WithLp 2 (Y × ℝ))).symm.toContinuousLinearMap.comp
    (block1.prod block23_lp)

@[simp] theorem M_clm_apply (𝓢 : IrnSetup X Y) (u : H X Y) :
    𝓢.M_clm u = 𝓢.M_apply u := rfl

/-- **Euler-type identity for `M`.** `⟨u, M u⟩ = ⟨x, P x⟩`: the skew
off-diagonal blocks cancel pairwise (the `A`/`A†` pair, the `c` pair,
and the `b` pair each contribute zero), leaving only the symmetric
`P`-block. -/
theorem inner_u_M (u : H X Y) :
    inner ℝ u (𝓢.M_apply u) =
      𝓢.Px_bilinform (𝓢.x_proj u) (𝓢.x_proj u) := by
  unfold M_apply Px_bilinform x_proj y_proj tau_proj
  simp only [WithLp.prod_inner_apply, WithLp.fst, WithLp.snd,
             inner_add_right, inner_neg_right, real_inner_smul_right,
             ContinuousLinearMap.adjoint_inner_right,
             RCLike.inner_apply, starRingEnd_apply, star_trivial]
  rw [real_inner_comm (𝓢.A u.ofLp.1) u.ofLp.2.ofLp.1,
      real_inner_comm 𝓢.c u.ofLp.1,
      real_inner_comm 𝓢.b u.ofLp.2.ofLp.1]
  ring

/-- The KKT operator `Q : H → H` from eq. (2.4):
$$ Q(u) = M u - \frac{1}{\tau}\!\big(0,\,0,\,x^\top P x\big)
        = M u - \big(Px_{\mathrm{bilinform}}(x, x) / \tau\big) \cdot e_\tau. $$
Defined only on `Cplus` (the `τ > 0` region) because the rational
correction `Px(x, x)/τ` is undefined at `τ = 0`. The `hu : u ∈ Cplus`
hypothesis is taken explicitly. -/
noncomputable def Q_apply (𝓢 : IrnSetup X Y) (u : H X Y)
    (_hu : u ∈ 𝓢.Cplus) : H X Y :=
  𝓢.M_apply u -
    (𝓢.Px_bilinform (𝓢.x_proj u) (𝓢.x_proj u) / 𝓢.tau_proj u) • 𝓢.e_τ

/-- **The `Q_eq` decomposition** — `Q u = M u - (Px(x,x)/τ) • e_τ` — is
the definition itself. -/
theorem Q_eq {u : H X Y} (hu : u ∈ 𝓢.Cplus) :
    𝓢.Q_apply u hu =
      𝓢.M_apply u -
        (𝓢.Px_bilinform (𝓢.x_proj u) (𝓢.x_proj u) / 𝓢.tau_proj u) • 𝓢.e_τ :=
  rfl

/-- **Euler-type identity for `Q_apply`.** `⟨u, Q_apply(u, hu)⟩ = 0` on
`Cplus`. -/
theorem inner_u_Q_apply {u : H X Y} (hu : u ∈ 𝓢.Cplus) :
    inner ℝ u (𝓢.Q_apply u hu) = (0 : ℝ) := by
  have hτ : 0 < 𝓢.tau_proj u := 𝓢.tau_proj_pos hu
  have hτ_ne : 𝓢.tau_proj u ≠ 0 := ne_of_gt hτ
  rw [𝓢.Q_eq hu, inner_sub_right, real_inner_smul_right,
      𝓢.inner_u_M, 𝓢.inner_u_e_tau]
  field_simp
  ring

/-- `y_proj` commutes with subtraction (linearity of the projection). -/
lemma y_proj_sub (u v : H X Y) :
    𝓢.y_proj (u - v) = 𝓢.y_proj u - 𝓢.y_proj v := by
  unfold y_proj
  simp

/-- The inner product of `u : H` with a y-block-lifted vector
`(0, yv, 0)` reduces to the inner of the y-component:
`⟨u, (0, yv, 0)⟩_H = ⟨y_proj u, yv⟩_Y`. -/
lemma inner_u_lifted_y (u : H X Y) (yv : Y) :
    inner ℝ u
      (WithLp.toLp 2 ((0 : X), WithLp.toLp 2 (yv, (0 : ℝ)))) =
    inner ℝ (𝓢.y_proj u) yv := by
  unfold y_proj
  simp only [WithLp.prod_inner_apply, inner_zero_right, zero_add, add_zero]
  rfl

/-- The y-projection is continuous (composition of `WithLp.snd` and
`WithLp.fst`). -/
lemma y_proj_continuous : Continuous 𝓢.y_proj := by
  unfold y_proj
  fun_prop

/-- The τ-projection is continuous (composition of two `WithLp.snd`). -/
lemma tau_proj_continuous : Continuous 𝓢.tau_proj := by
  unfold tau_proj
  fun_prop

/-- `y_proj` is surjective: for any `y ∈ Y`, take `(0, y, 0) ∈ H`. -/
theorem y_proj_surjective : Function.Surjective 𝓢.y_proj := by
  intro y
  refine ⟨WithLp.toLp 2 ((0 : X), WithLp.toLp 2 (y, (0 : ℝ))), ?_⟩
  rfl

/-- `y_proj` is an open map: it's a surjective continuous linear map
between finite-dimensional inner-product spaces, so the
finite-dimensional open mapping theorem applies. -/
theorem y_proj_isOpenMap : IsOpenMap 𝓢.y_proj := by
  -- y_proj agrees with the CLM y_proj_linear; the CLM's underlying
  -- LinearMap is surjective and lands in finite-dim, so it's open.
  have h_eq : 𝓢.y_proj = ⇑(IrnSetup.y_proj_linear : H X Y →L[ℝ] Y) := by
    funext u
    exact (𝓢.y_proj_linear_apply u).symm
  rw [h_eq]
  exact (IrnSetup.y_proj_linear : H X Y →L[ℝ] Y).toLinearMap.isOpenMap_of_finiteDimensional
    (h_eq ▸ 𝓢.y_proj_surjective)

/-- The lifted cone for `f_lhscb` on `H`: `y_proj⁻¹(K)`. Closed since
`y_proj` is continuous and `K` is closed (as a `ProperCone`). -/
def K_f_lifted (𝓢 : IrnSetup X Y) : Set (H X Y) :=
  𝓢.y_proj ⁻¹' (𝓢.K : Set Y)

/-- `interior (K_f_lifted) = y_proj⁻¹(interior K)`. Follows from
`y_proj` being an open continuous map. -/
theorem interior_K_f_lifted :
    interior 𝓢.K_f_lifted = 𝓢.y_proj ⁻¹' (interior (𝓢.K : Set Y)) :=
  (𝓢.y_proj_isOpenMap.preimage_interior_eq_interior_preimage
    𝓢.y_proj_continuous (𝓢.K : Set Y)).symm

/-- **Lift of `fBarrier` to `H`.** The user's `ν`-LHSCB `f` on `Y` extends
to a `ν`-LHSCB `f_lhscb` on `H = X × Y × ℝ` (with respect to the
lifted cone `K_f_lifted = y_proj⁻¹(K)`) by acting only on the y-block:
`f_lift(x, y, τ) := f(y)`, with gradient `(0, ∇f(y), 0)`. The Euler
identity, gradient monotonicity, and log-homogeneity transport from
`fBarrier`. -/
noncomputable def f_lhscb : LHSCB (H X Y) 𝓢.K_f_lifted 𝓢.ν where
  f u := 𝓢.fBarrier.f (𝓢.y_proj u)
  contDiff := by
    -- `f_lhscb.f = fBarrier.f ∘ y_proj_linear`. Smoothness transports
    -- along the continuous linear map.
    rw [𝓢.interior_K_f_lifted]
    exact 𝓢.fBarrier.contDiff.comp_continuousLinearMap
      (IrnSetup.y_proj_linear : H X Y →L[ℝ] Y)
  self_concordant := by
    -- Self-concordance of `fBarrier.f ∘ y_proj_linear` follows from
    -- self-concordance of `fBarrier.f` via the chain rule for
    -- iterated derivatives composed with a CLM.
    have key := LHSCB.self_concordant_comp_right_clm
      (s := interior (𝓢.K : Set Y))
      isOpen_interior 𝓢.fBarrier.contDiff 𝓢.fBarrier.self_concordant
      (IrnSetup.y_proj_linear : H X Y →L[ℝ] Y)
    -- `interior K_f_lifted = y_proj_linear ⁻¹' interior K`.
    have hset : 𝓢.K_f_lifted = (IrnSetup.y_proj_linear : H X Y →L[ℝ] Y) ⁻¹' (𝓢.K : Set Y) := rfl
    intro x hx h
    rw [𝓢.interior_K_f_lifted] at hx
    have := key x hx h
    -- `f_lhscb.f u = fBarrier.f (y_proj u) = (fBarrier.f ∘ y_proj_linear) u`.
    -- Both sides match definitionally.
    rw [𝓢.interior_K_f_lifted]
    exact this
  log_homog := by
    intros u hu t ht
    rw [𝓢.interior_K_f_lifted] at hu
    show 𝓢.fBarrier.f (𝓢.y_proj (t • u)) =
      𝓢.fBarrier.f (𝓢.y_proj u) - (𝓢.ν : ℝ) * Real.log t
    have h_proj : 𝓢.y_proj (t • u) = t • 𝓢.y_proj u := by
      unfold y_proj
      simp
    rw [h_proj]
    exact 𝓢.fBarrier.log_homog (𝓢.y_proj u) hu t ht
  barrier := by
    intros x hx
    -- `K` is closed (as a `ProperCone`), so `K_f_lifted = y_proj⁻¹(K)` is
    -- closed and `x ∈ K_f_lifted`. Combined with `x ∉ interior K_f_lifted
    -- = y_proj⁻¹(interior K)`, this gives `y_proj x ∈ frontier K`.
    have hK_closed : IsClosed (𝓢.K : Set Y) := 𝓢.K.isClosed
    have hKf_closed : IsClosed 𝓢.K_f_lifted :=
      hK_closed.preimage 𝓢.y_proj_continuous
    have hx_in_Kf : x ∈ 𝓢.K_f_lifted := by
      have := frontier_subset_closure hx
      rwa [hKf_closed.closure_eq] at this
    have hx_not_int : x ∉ interior 𝓢.K_f_lifted := hx.2
    rw [𝓢.interior_K_f_lifted] at hx_not_int
    have h_yp_frontier : 𝓢.y_proj x ∈ frontier (𝓢.K : Set Y) :=
      ⟨subset_closure hx_in_Kf, hx_not_int⟩
    -- Lift `fBarrier.barrier` along `y_proj` using continuity and the
    -- already-proved `interior K_f_lifted = y_proj⁻¹(interior K)`.
    rw [𝓢.interior_K_f_lifted]
    have h_yp_tendsto :
        Filter.Tendsto 𝓢.y_proj
          (nhdsWithin x (𝓢.y_proj ⁻¹' interior (𝓢.K : Set Y)))
          (nhdsWithin (𝓢.y_proj x) (interior (𝓢.K : Set Y))) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨(𝓢.y_proj_continuous.tendsto x).mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact hu
    exact (𝓢.fBarrier.barrier (𝓢.y_proj x) h_yp_frontier).comp h_yp_tendsto

/-- **Totalised `Q`.** A version of `Q_apply` extended to all of `H`
(using Lean's division-by-zero-is-zero convention outside `Cplus`).
Only meaningful on `Cplus`; provided for compatibility with
`IrnSetup.Q : H → H` (which is a total function). -/
noncomputable def Q (𝓢 : IrnSetup X Y) (u : H X Y) : H X Y :=
  𝓢.M_apply u -
    (𝓢.Px_bilinform (𝓢.x_proj u) (𝓢.x_proj u) / 𝓢.tau_proj u) • 𝓢.e_τ

/-- `Q` agrees with `Q_apply` on `Cplus` (where Q is mathematically
defined). -/
theorem Q_eq_Q_apply {u : H X Y} (hu : u ∈ 𝓢.Cplus) :
    𝓢.Q u = 𝓢.Q_apply u hu := rfl

/-- **Euler-type identity for `Q`** (total form). `⟨u, Q(u)⟩ = 0` on
`Cplus`: the matrix part contributes `Px(x, x)` (via `inner_u_M`) and
the rational correction `-(Px(x, x)/τ) · τ = -Px(x, x)` cancels. -/
theorem inner_u_Q {u : H X Y} (hu : u ∈ 𝓢.Cplus) :
    inner ℝ u (𝓢.Q u) = (0 : ℝ) := by
  rw [𝓢.Q_eq_Q_apply hu]
  exact 𝓢.inner_u_Q_apply hu

/-- **Totalised `φ`.** The barrier-gradient `φ = ∇f + ∇g` lifted to
`H`, where `∇g(u) = (-1/tau_proj u) • e_τ` is the τ-component of the
log barrier's gradient. Total on all of `H` (Lean's
division-by-zero-is-zero convention applies outside `Cplus`). -/
noncomputable def φ (𝓢 : IrnSetup X Y) (u : H X Y) : H X Y :=
  𝓢.f_lhscb.grad u + (-1 / 𝓢.tau_proj u) • 𝓢.e_τ

/-- `C_interior` is in the lifted f-barrier interior: if `y_proj u ∈
int K` then `u ∈ interior K_f_lifted`. -/
theorem C_interior_subset_f_lhscb_interior :
    𝓢.C_interior ⊆ interior 𝓢.K_f_lifted := fun u hu => by
  rw [𝓢.interior_K_f_lifted]
  exact hu.1

/-! ### Sphere radius and derived norm facts -/

/-- Sphere radius `r = √(ν+1)`. -/
noncomputable def r : ℝ := Real.sqrt ((𝓢.ν : ℝ) + 1)

theorem r_sq : 𝓢.r ^ 2 = (𝓢.ν : ℝ) + 1 := by
  unfold r
  exact Real.sq_sqrt (by positivity)

theorem r_pos : 0 < 𝓢.r := by
  unfold r
  exact Real.sqrt_pos.mpr (by positivity)

/-! ### `Cplus` topology -/

/-- `Cplus = {u | 0 < tau_proj u}` is open: it's the preimage of
`(0, ∞)` under the continuous linear functional `tau_proj_linear`. -/
theorem Cplus_open : IsOpen 𝓢.Cplus := by
  have h_eq : 𝓢.Cplus =
      (IrnSetup.tau_proj_linear : H X Y →L[ℝ] ℝ) ⁻¹' Set.Ioi 0 := by
    ext u
    show 0 < 𝓢.tau_proj u ↔ 0 < tau_proj_linear u
    rw [tau_proj_linear_apply]
  rw [h_eq]
  exact (IrnSetup.tau_proj_linear : H X Y →L[ℝ] ℝ).continuous.isOpen_preimage
    _ isOpen_Ioi

/-! ### `Q` monotonicity (Proposition 1) -/

/-- **Proposition 1 (Monotonicity of `Q`).** Direct calculation gives
`⟨u₁ - u₂, Q(u₁) - Q(u₂)⟩ = τ₁τ₂(z₁ - z₂)⊤ P (z₁ - z₂) ≥ 0`. The
τ-rescaling is captured by `Px_quad_form_psd`. -/
theorem Q_monotone (u : H X Y) (hu : u ∈ 𝓢.Cplus)
    (v : H X Y) (hv : v ∈ 𝓢.Cplus) :
    0 ≤ inner ℝ (u - v) (𝓢.Q u - 𝓢.Q v) := by
  have hτu : 0 < 𝓢.tau_proj u := 𝓢.tau_proj_pos hu
  have hτv : 0 < 𝓢.tau_proj v := 𝓢.tau_proj_pos hv
  have hτu_ne : 𝓢.tau_proj u ≠ 0 := ne_of_gt hτu
  have hτv_ne : 𝓢.tau_proj v ≠ 0 := ne_of_gt hτv
  have hτuv : 0 < 𝓢.tau_proj u * 𝓢.tau_proj v := mul_pos hτu hτv
  -- Unfold Q to M_apply minus the rational correction.
  show 0 ≤ inner ℝ (u - v)
    ((𝓢.M_apply u - (𝓢.Px_bilinform (𝓢.x_proj u) (𝓢.x_proj u) /
      𝓢.tau_proj u) • 𝓢.e_τ) -
     (𝓢.M_apply v - (𝓢.Px_bilinform (𝓢.x_proj v) (𝓢.x_proj v) /
      𝓢.tau_proj v) • 𝓢.e_τ))
  -- Use the M_clm packaging to repackage M_apply via M_clm's linearity:
  -- M_apply u - M_apply v = M_clm (u - v) (since M_clm_apply is rfl).
  have h_arrange :
      (𝓢.M_apply u - (𝓢.Px_bilinform (𝓢.x_proj u) (𝓢.x_proj u) /
        𝓢.tau_proj u) • 𝓢.e_τ) -
      (𝓢.M_apply v - (𝓢.Px_bilinform (𝓢.x_proj v) (𝓢.x_proj v) /
        𝓢.tau_proj v) • 𝓢.e_τ) =
      𝓢.M_clm (u - v) -
        ((𝓢.Px_bilinform (𝓢.x_proj u) (𝓢.x_proj u) / 𝓢.tau_proj u) -
          (𝓢.Px_bilinform (𝓢.x_proj v) (𝓢.x_proj v) / 𝓢.tau_proj v)) • 𝓢.e_τ := by
    rw [show 𝓢.M_apply u = 𝓢.M_clm u from rfl,
        show 𝓢.M_apply v = 𝓢.M_clm v from rfl,
        map_sub 𝓢.M_clm]
    module
  rw [h_arrange, inner_sub_right, inner_smul_right]
  -- ⟨u-v, M(u-v)⟩ = Px(x(u-v), x(u-v))
  have h_x_sub : 𝓢.x_proj (u - v) = 𝓢.x_proj u - 𝓢.x_proj v := by
    unfold x_proj
    simp
  have h_inner_M : inner ℝ (u - v) (𝓢.M_clm (u - v)) =
      𝓢.Px_bilinform (𝓢.x_proj u - 𝓢.x_proj v) (𝓢.x_proj u - 𝓢.x_proj v) := by
    rw [show 𝓢.M_clm (u - v) = 𝓢.M_apply (u - v) from rfl, 𝓢.inner_u_M]
    rw [h_x_sub]
  rw [h_inner_M]
  -- Expand `Px(x_u - x_v, x_u - x_v)` bilinearly.
  set xu := 𝓢.x_proj u
  set xv := 𝓢.x_proj v
  have h_Px_expand : 𝓢.Px_bilinform (xu - xv) (xu - xv) =
      𝓢.Px_bilinform xu xu - 2 * 𝓢.Px_bilinform xu xv +
      𝓢.Px_bilinform xv xv := by
    show inner ℝ (xu - xv) (𝓢.P (xu - xv)) =
      inner ℝ xu (𝓢.P xu) - 2 * inner ℝ xu (𝓢.P xv) +
      inner ℝ xv (𝓢.P xv)
    rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right]
    have h_sym : inner ℝ xv (𝓢.P xu) = inner ℝ xu (𝓢.P xv) := by
      rw [← 𝓢.P_symm, real_inner_comm]
    rw [h_sym]
    ring
  rw [h_Px_expand]
  -- `⟨u - v, e_τ⟩ = τ_u - τ_v`.
  have h_inner_etau : inner ℝ (u - v) 𝓢.e_τ = 𝓢.tau_proj u - 𝓢.tau_proj v := by
    rw [inner_sub_left, 𝓢.inner_u_e_tau, 𝓢.inner_u_e_tau]
  rw [h_inner_etau]
  -- Algebraic regrouping into the τ-rescaled PSD form.
  have h_psd :
      0 ≤ 𝓢.tau_proj v ^ 2 * 𝓢.Px_bilinform xu xu -
          2 * 𝓢.tau_proj u * 𝓢.tau_proj v * 𝓢.Px_bilinform xu xv +
          𝓢.tau_proj u ^ 2 * 𝓢.Px_bilinform xv xv :=
    𝓢.Px_quad_form_psd xu xv (𝓢.tau_proj u) (𝓢.tau_proj v)
  have h_id :
      𝓢.Px_bilinform xu xu - 2 * 𝓢.Px_bilinform xu xv +
        𝓢.Px_bilinform xv xv -
          (𝓢.Px_bilinform xu xu / 𝓢.tau_proj u -
            𝓢.Px_bilinform xv xv / 𝓢.tau_proj v) *
              (𝓢.tau_proj u - 𝓢.tau_proj v) =
        (𝓢.tau_proj v ^ 2 * 𝓢.Px_bilinform xu xu -
          2 * 𝓢.tau_proj u * 𝓢.tau_proj v * 𝓢.Px_bilinform xu xv +
          𝓢.tau_proj u ^ 2 * 𝓢.Px_bilinform xv xv) /
          (𝓢.tau_proj u * 𝓢.tau_proj v) := by
    field_simp
    ring
  rw [h_id]
  exact div_nonneg h_psd (le_of_lt hτuv)

/-! ### The combined `(ν+1)`-LHSCB `F = f + g` -/

/-- `tau_proj` is surjective: for any `r ∈ ℝ`, take `(0, 0, r) ∈ H`. -/
theorem tau_proj_surjective : Function.Surjective 𝓢.tau_proj := by
  intro r
  refine ⟨WithLp.toLp 2 ((0 : X), WithLp.toLp 2 ((0 : Y), r)), ?_⟩
  rfl

/-- `tau_proj` is an open map (surjective continuous linear functional
on finite-dimensional inner-product spaces). -/
theorem tau_proj_isOpenMap : IsOpenMap 𝓢.tau_proj := by
  have h_eq : 𝓢.tau_proj = ⇑(IrnSetup.tau_proj_linear : H X Y →L[ℝ] ℝ) := by
    funext u
    exact (𝓢.tau_proj_linear_apply u).symm
  rw [h_eq]
  exact (IrnSetup.tau_proj_linear : H X Y →L[ℝ] ℝ).toLinearMap.isOpenMap_of_finiteDimensional
    (h_eq ▸ 𝓢.tau_proj_surjective)

/-- The lifted cone for `g_lhscb`: `tau_proj⁻¹([0, ∞)) = {u | 0 ≤
tau_proj u}`. -/
def K_g_lifted (𝓢 : IrnSetup X Y) : Set (H X Y) :=
  {u | 0 ≤ 𝓢.tau_proj u}

theorem interior_K_g_lifted : interior 𝓢.K_g_lifted = 𝓢.Cplus := by
  -- K_g_lifted = tau_proj ⁻¹' (Set.Ici 0). Interior of preimage =
  -- preimage of interior (since tau_proj is open continuous), and
  -- interior (Set.Ici 0) = Set.Ioi 0 in ℝ.
  show interior (𝓢.tau_proj ⁻¹' Set.Ici 0) = {u | 0 < 𝓢.tau_proj u}
  rw [← 𝓢.tau_proj_isOpenMap.preimage_interior_eq_interior_preimage
        𝓢.tau_proj_continuous (Set.Ici 0), interior_Ici]
  rfl

/-- The concrete `1`-LHSCB `g(τ) = -log τ` lifted to `H` with respect
to the lifted cone `K_g_lifted = {u | 0 ≤ tau_proj u}`. The gradient
is `(-1/tau_proj u) • e_τ`; Euler uses `inner_u_e_tau`; monotonicity
uses `(τ_u - τ_v)² / (τ_u τ_v) ≥ 0`. -/
noncomputable def g_lhscb : LHSCB (H X Y) 𝓢.K_g_lifted 1 where
  f := fun u => -Real.log (𝓢.tau_proj u)
  contDiff := by
    -- `-Real.log ∘ tau_proj_linear` is `C³` on `Cplus = {τ > 0}` since
    -- `Real.log` is `C^∞` away from 0 and `tau_proj` is a CLM.
    rw [𝓢.interior_K_g_lifted]
    intro u hu
    have hτ : 0 < 𝓢.tau_proj u := hu
    have h_log : ContDiffAt ℝ 3 Real.log (𝓢.tau_proj u) :=
      Real.contDiffAt_log.mpr (ne_of_gt hτ)
    have h_tau : ContDiffAt ℝ 3 (fun u : H X Y => 𝓢.tau_proj u) u := by
      have : ContDiffAt ℝ 3 (IrnSetup.tau_proj_linear : H X Y →L[ℝ] ℝ) u :=
        (IrnSetup.tau_proj_linear : H X Y →L[ℝ] ℝ).contDiff.contDiffAt
      simpa using this
    exact ((h_log.comp u h_tau).neg).contDiffWithinAt
  self_concordant := by
    -- For `-log t` on `t > 0`: `D²(-log) = 1/t²`, `D³(-log) = -2/t³`,
    -- so `(D³)² = 4/t⁶ = 4·(1/t²)³` — the SC bound holds with
    -- equality. Lifting through the CLM `tau_proj` requires the
    -- iteratedFDeriv chain rule for linear maps. Deferred.
    intro x _hx h
    sorry
  log_homog := by
    intros u hu t ht
    rw [𝓢.interior_K_g_lifted] at hu
    have hτ : 0 < 𝓢.tau_proj u := 𝓢.tau_proj_pos hu
    have h_proj : 𝓢.tau_proj (t • u) = t * 𝓢.tau_proj u := by
      unfold tau_proj
      simp
    show -Real.log (𝓢.tau_proj (t • u)) =
      -Real.log (𝓢.tau_proj u) - ((1 : ℕ) : ℝ) * Real.log t
    rw [h_proj, Real.log_mul (ne_of_gt ht) (ne_of_gt hτ)]
    push_cast
    ring
  barrier := by
    intros x hx
    -- Extract `tau_proj x = 0` from `x ∈ frontier K_g_lifted`.
    have h_K_closed : IsClosed 𝓢.K_g_lifted :=
      isClosed_Ici.preimage 𝓢.tau_proj_continuous
    have h_x_in_K : x ∈ 𝓢.K_g_lifted := by
      have := frontier_subset_closure hx
      rwa [h_K_closed.closure_eq] at this
    have h_x_not_int : x ∉ interior 𝓢.K_g_lifted := hx.2
    rw [𝓢.interior_K_g_lifted] at h_x_not_int
    have h_tau_zero : 𝓢.tau_proj x = 0 := by
      have h_ge : 0 ≤ 𝓢.tau_proj x := h_x_in_K
      have h_le : 𝓢.tau_proj x ≤ 0 := not_lt.mp h_x_not_int
      linarith
    -- Show `-log (tau_proj u) → +∞` as `u → x` within `Cplus`.
    rw [𝓢.interior_K_g_lifted]
    -- Step 1: `tau_proj : 𝓝[Cplus] x → 𝓝[Ioi 0] 0`.
    have h_tau_tendsto :
        Filter.Tendsto 𝓢.tau_proj (nhdsWithin x 𝓢.Cplus)
          (nhdsWithin 0 (Set.Ioi 0)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h : Filter.Tendsto 𝓢.tau_proj (nhds x) (nhds (𝓢.tau_proj x)) :=
          𝓢.tau_proj_continuous.tendsto x
        rw [h_tau_zero] at h
        exact h.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with u hu
        exact hu
    -- Step 2: `-Real.log : 𝓝[Ioi 0] 0 → atTop`.
    have h_log_tendsto :
        Filter.Tendsto (fun r : ℝ => -Real.log r)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atTop :=
      Filter.tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
    -- Compose.
    exact h_log_tendsto.comp h_tau_tendsto

/-- The combined `(ν+1)`-LHSCB `F = f + g` driving the IRN central path.
Cone: `K_f_lifted ∩ K_g_lifted`, whose interior is `C_interior`. -/
noncomputable def F_lhscb :
    LHSCB (H X Y) (𝓢.K_f_lifted ∩ 𝓢.K_g_lifted) (𝓢.ν + 1) :=
  𝓢.f_lhscb.add 𝓢.g_lhscb

/-- `C_interior` equals `interior (K_f_lifted ∩ K_g_lifted)` — the
domain of `F_lhscb`. -/
theorem C_interior_subset_F_interior :
    𝓢.C_interior ⊆ interior (𝓢.K_f_lifted ∩ 𝓢.K_g_lifted) := fun u hu => by
  rw [interior_inter, 𝓢.interior_K_f_lifted, 𝓢.interior_K_g_lifted]
  exact ⟨hu.1, hu.2⟩

/-- **Bridge lemma: closed form of `g_lhscb.grad`.** The derived
(Fréchet-based) gradient of `g_lhscb` on `C_interior = {τ > 0}`
agrees with the explicit `(-1/τ) • e_τ`. Proof uses the chain rule
for `fderiv (-Real.log ∘ tau_proj_linear)` plus the fact that
`tau_proj_linear` is its own derivative and that `e_τ` is the
Riesz vector of `tau_proj_linear`. -/
theorem g_lhscb_grad_apply (u : H X Y) (hu : u ∈ 𝓢.C_interior) :
    𝓢.g_lhscb.grad u = (-1 / 𝓢.tau_proj u) • 𝓢.e_τ := by
  have hτ : 0 < 𝓢.tau_proj u := hu.2
  have hτ_ne : 𝓢.tau_proj u ≠ 0 := ne_of_gt hτ
  -- Apply `toDual` to both sides; `(toDual).symm` cancels on LHS.
  apply (InnerProductSpace.toDual ℝ (H X Y)).injective
  show (InnerProductSpace.toDual ℝ (H X Y)) ((InnerProductSpace.toDual ℝ (H X Y)).symm
        (fderiv ℝ (fun v => -Real.log (𝓢.tau_proj v)) u))
       = (InnerProductSpace.toDual ℝ (H X Y)) ((-1 / 𝓢.tau_proj u) • 𝓢.e_τ)
  rw [LinearIsometryEquiv.apply_symm_apply]
  -- Compute fderiv via chain rule: log ∘ tau_proj_linear.
  have h_tau_fd : HasFDerivAt (fun v : H X Y => 𝓢.tau_proj v)
      (IrnSetup.tau_proj_linear : H X Y →L[ℝ] ℝ) u :=
    (IrnSetup.tau_proj_linear : H X Y →L[ℝ] ℝ).hasFDerivAt
  have h_log_fd : HasFDerivAt Real.log
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (𝓢.tau_proj u)⁻¹) (𝓢.tau_proj u) :=
    (Real.hasDerivAt_log hτ_ne).hasFDerivAt
  have h_neg : HasFDerivAt (fun v => -Real.log (𝓢.tau_proj v))
      (-((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (𝓢.tau_proj u)⁻¹).comp
        (IrnSetup.tau_proj_linear : H X Y →L[ℝ] ℝ))) u :=
    (h_log_fd.comp u h_tau_fd).neg
  rw [h_neg.fderiv]
  -- Now: -((smulRight 1 (1/τ)).comp tau_proj_linear) = toDual ((-1/τ) • e_τ).
  -- Both sides are CLMs `H →L[ℝ] ℝ`; compare pointwise.
  ext v
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply,
    InnerProductSpace.toDual_apply_apply, inner_smul_left, conj_trivial,
    𝓢.tau_proj_linear_apply]
  rw [real_inner_comm, 𝓢.inner_u_e_tau, smul_eq_mul]
  field_simp

/-- The IRN setup's `φ` equals the combined LHSCB gradient on
`C_interior`. -/

theorem phi_eq_F_grad (u : H X Y) (hu : u ∈ 𝓢.C_interior) :
    𝓢.φ u = 𝓢.F_lhscb.grad u := by
  show 𝓢.f_lhscb.grad u + (-1 / 𝓢.tau_proj u) • 𝓢.e_τ
    = (𝓢.f_lhscb.add 𝓢.g_lhscb).grad u
  rw [← 𝓢.g_lhscb_grad_apply u hu]
  have hu' : u ∈ interior 𝓢.K_f_lifted ∩ interior 𝓢.K_g_lifted := by
    rw [𝓢.interior_K_f_lifted, 𝓢.interior_K_g_lifted]
    exact ⟨hu.1, hu.2⟩
  exact (LHSCB.add_grad 𝓢.f_lhscb 𝓢.g_lhscb hu').symm

/-- **Euler-type identity for `φ`** (Proposition 3):
`⟨u, φ(u)⟩ = -(ν+1)` on `C_interior`. -/
theorem inner_u_phi (u : H X Y) (hu : u ∈ 𝓢.C_interior) :
    inner ℝ u (𝓢.φ u) = -((𝓢.ν : ℝ) + 1) := by
  rw [𝓢.phi_eq_F_grad u hu,
    𝓢.F_lhscb.euler u (𝓢.C_interior_subset_F_interior hu)]
  push_cast
  ring

/-- **Monotonicity of `φ`** on `C_interior`. -/
theorem phi_monotone (u : H X Y) (hu : u ∈ 𝓢.C_interior)
    (v : H X Y) (hv : v ∈ 𝓢.C_interior) :
    0 ≤ inner ℝ (u - v) (𝓢.φ u - 𝓢.φ v) := by
  rw [𝓢.phi_eq_F_grad u hu, 𝓢.phi_eq_F_grad v hv]
  -- `interior (K_f_lifted ∩ K_g_lifted) = Cplus ∩ y_proj⁻¹(interior K)` is
  -- convex (preimage of convex via linear, intersected with half-space).
  have h_conv : Convex ℝ (interior (𝓢.K_f_lifted ∩ 𝓢.K_g_lifted)) := by
    rw [interior_inter, 𝓢.interior_K_f_lifted, 𝓢.interior_K_g_lifted]
    refine Convex.inter ?_ ?_
    · exact (𝓢.K.convex.interior).linear_preimage
        (IrnSetup.y_proj_linear : H X Y →L[ℝ] Y).toLinearMap
    · -- Cplus = tau_proj ⁻¹' Ioi 0; convex via linear preimage.
      have h_ioi_conv : Convex ℝ (Set.Ioi (0:ℝ)) := convex_Ioi 0
      exact h_ioi_conv.linear_preimage
        (IrnSetup.tau_proj_linear : H X Y →L[ℝ] ℝ).toLinearMap
  exact 𝓢.F_lhscb.grad_monotone h_conv u (𝓢.C_interior_subset_F_interior hu) v
    (𝓢.C_interior_subset_F_interior hv)

end IrnSetup

end Irn
