/-
# Polarization of a symmetric multilinear form by a PSD bilinear form

Let `A : V^k → ℝ` be a symmetric (continuous) `k`-linear form and
`B : V × V → ℝ` a (continuous) bilinear form on a normed real vector
space `V` with `0 ≤ B[h, h]` for every `h` (positive
semidefiniteness on the diagonal). If, for some constant `α ≥ 0`,
the diagonal of `A` is bounded by `α · B^{k/2}`:

  `|A[h, …, h]| ≤ α · (√B[h, h])^k`   for every `h : V`,

then the polarized bound

  `|A[h₁, …, h_k]| ≤ α · ∏ᵢ √B[hᵢ, hᵢ]`

holds for all `h₁, …, h_k : V`.

This is the classical polarization principle for symmetric forms
relative to a PSD bilinear form — the constant `α` is preserved in
passing from the diagonal to the full polarization. The proof rests
on the standard polarization identity for symmetric `k`-linear forms
together with a rescaling argument `hᵢ ↦ λᵢ · hᵢ` that minimizes the
upper bound across the diagonals.

## File layout

* `IsSymm` — permutation-invariance predicate for a continuous
  multilinear map on a constant Pi-type `Fin k → V`.
* `iteratedFDerivWithin_three_isSymm` — full `S₃` symmetry of
  `D³f(x)` for any real-valued `C³` function `f` on an open set
  `s ⊆ V` and any `x ∈ s`. Built from two Schwarz-style transpositions
  (swap of slots `(0 1)` from `IsSymmSndFDerivWithinAt` of `∇f`; swap
  of slots `(1 2)` from a chain-rule lift of `IsSymmSndFDerivWithinAt`
  of `f` at every point of `s`), extended to all of `S₃` via
  `Equiv.Perm.swap_induction_on`.
* `multilinear_polarization_of_diagonal_bound` — the abstract
  polarization theorem above, stated for any `k : ℕ`.
* `trilinear_polarization_of_diagonal_bound` — the `k = 3` corollary,
  packaged in the precise form consumed by
  `Irn.LHSCB.self_concordant_polarization` (the trilinear
  self-concordance bound at a fixed interior point).

Only the polarization statements (`multilinear_…` and `trilinear_…`)
are currently scaffolded with `sorry`; the symmetry of `D³f` is
proved here, and the application into `Dikin.lean` is formalized.
-/

import Mathlib

namespace Irn

open scoped BigOperators

namespace TrilinForm

/-- A continuous `k`-linear form on a constant Pi-type `Fin k → V` is
**symmetric** if it is invariant under every permutation of its
arguments. Permutation-invariance via `Equiv.Perm (Fin k)` is
equivalent to transposition-invariance for `k ≥ 2`. -/
def IsSymm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin k => V) ℝ) : Prop :=
  ∀ (v : Fin k → V) (σ : Equiv.Perm (Fin k)), A (v ∘ σ) = A v

/-! ### Symmetry of the third iterated derivative on an open set

For a real-valued `C³` function `f` on an open set `s ⊆ V`, the third
iterated derivative `D³f(x)` at any `x ∈ s` is a symmetric trilinear
form. Mathlib provides the symmetry of the *second* derivative
(`IsSymmSndFDerivWithinAt`); the third-derivative case is assembled
here from:

* swap of slots `(0 1)`: `IsSymmSndFDerivWithinAt` applied to the
  gradient `∇f := fderivWithin ℝ f s` (which is `C²` since `f` is
  `C³`), unfolding `D³f` via `iteratedFDerivWithin_succ_apply_right`;
* swap of slots `(1 2)`: `IsSymmSndFDerivWithinAt` applied to `f` at
  every `y ∈ s`, then lifted through `fderivWithin` via the chain
  rule with the evaluation `ContinuousMultilinearMap.apply` and the
  congruence of derivatives of equal-on-`s` functions
  (`fderivWithin_congr'`).

These two transpositions generate the symmetric group `S₃` and
`Equiv.Perm.swap_induction_on` then extends invariance to all of
`S₃`. -/

section IteratedFDerivWithinSymm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {f : V → ℝ} {s : Set V}

/-- For a real-valued `C³` function `f` on an open set `s ⊆ V` and
any `y ∈ s`, the second iterated derivative `D²f(y)` is symmetric in
its two arguments. Direct consequence of `IsSymmSndFDerivWithinAt`
applied pointwise (since `s` is open, `y ∈ s = interior s ⊆
closure (interior s)`). -/
private lemma iteratedFDerivWithin_two_swap
    (hs_open : IsOpen s) (hf : ContDiffOn ℝ 3 f s)
    {y : V} (hy : y ∈ s) (a b : V) :
    iteratedFDerivWithin ℝ 2 f s y ![a, b]
      = iteratedFDerivWithin ℝ 2 f s y ![b, a] := by
  have hs_unique : UniqueDiffOn ℝ s := hs_open.uniqueDiffOn
  have h_y_closure : y ∈ closure (interior s) := by
    rw [hs_open.interior_eq]; exact subset_closure hy
  have h_f_C2_at_y : ContDiffWithinAt ℝ 2 f s y :=
    (hf.contDiffWithinAt hy).of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have h_symm : IsSymmSndFDerivWithinAt ℝ f s y :=
    h_f_C2_at_y.isSymmSndFDerivWithinAt
      (by rw [minSmoothness_of_isRCLikeNormedField])
      hs_unique h_y_closure hy
  exact h_symm.iteratedFDerivWithin_cons hs_unique hy

/-- For a real-valued `C³` function `f` on an open set `s ⊆ V` and
any `x ∈ s`, the second iterated derivative of `∇f := fderivWithin ℝ
f s` at `x` is symmetric in its two arguments. Uses that `∇f` is `C²`
on `s` (one less derivative than `f`) and applies
`IsSymmSndFDerivWithinAt` to `∇f`. -/
private lemma iteratedFDerivWithin_two_fderiv_swap
    (hs_open : IsOpen s) (hf : ContDiffOn ℝ 3 f s)
    {x : V} (hx : x ∈ s) (a b : V) :
    iteratedFDerivWithin ℝ 2 (fderivWithin ℝ f s) s x ![a, b]
      = iteratedFDerivWithin ℝ 2 (fderivWithin ℝ f s) s x ![b, a] := by
  have hs_unique : UniqueDiffOn ℝ s := hs_open.uniqueDiffOn
  have h_x_closure : x ∈ closure (interior s) := by
    rw [hs_open.interior_eq]; exact subset_closure hx
  have h_Df_C2 : ContDiffOn ℝ 2 (fderivWithin ℝ f s) s :=
    hf.fderivWithin hs_unique (by norm_num : (2 + 1 : WithTop ℕ∞) ≤ 3)
  have h_Df_C2_at_x : ContDiffWithinAt ℝ 2 (fderivWithin ℝ f s) s x :=
    h_Df_C2.contDiffWithinAt hx
  have h_symm : IsSymmSndFDerivWithinAt ℝ (fderivWithin ℝ f s) s x :=
    h_Df_C2_at_x.isSymmSndFDerivWithinAt
      (by rw [minSmoothness_of_isRCLikeNormedField])
      hs_unique h_x_closure hx
  exact h_symm.iteratedFDerivWithin_cons hs_unique hx

/-- Last-two-slot swap of `D³f(x)` (the transposition `(1 2)`).

Unfolding via `iteratedFDerivWithin_succ_apply_left` (which is `rfl`)
reduces this to showing that `fderivWithin ℝ D²f s x (a) :
CMM(Fin 2 → V) ℝ` is symmetric in its two arguments — a fact obtained
by lifting the pointwise symmetry of `D²f(y)`
(`iteratedFDerivWithin_two_swap`) along the chain rule with the
evaluation `ContinuousMultilinearMap.apply ℝ _ ℝ ![b, c]`. -/
private lemma iteratedFDerivWithin_three_swap_last_two
    (hs_open : IsOpen s) (hf : ContDiffOn ℝ 3 f s)
    {x : V} (hx : x ∈ s) (v : Fin 3 → V) :
    iteratedFDerivWithin ℝ 3 f s x (v ∘ Equiv.swap (1 : Fin 3) 2)
      = iteratedFDerivWithin ℝ 3 f s x v := by
  have hs_unique : UniqueDiffOn ℝ s := hs_open.uniqueDiffOn
  have h_unique_at_x : UniqueDiffWithinAt ℝ s x := hs_unique x hx
  have h_D2_diff :
      DifferentiableWithinAt ℝ (iteratedFDerivWithin ℝ 2 f s) s x :=
    (hf.differentiableOn_iteratedFDerivWithin (m := 2)
      (by norm_num : ((2 : ℕ) : WithTop ℕ∞) < 3) hs_unique) x hx
  -- `iteratedFDerivWithin_succ_apply_left` is `rfl`; unfold via `show`.
  show fderivWithin ℝ (iteratedFDerivWithin ℝ 2 f s) s x
         ((v ∘ Equiv.swap (1 : Fin 3) 2) 0)
         (Fin.tail (v ∘ Equiv.swap (1 : Fin 3) 2))
       = fderivWithin ℝ (iteratedFDerivWithin ℝ 2 f s) s x (v 0)
         (Fin.tail v)
  -- Compute `(v ∘ swap 1 2) 0 = v 0` and the two tails.
  have h_swap_0 : (v ∘ Equiv.swap (1 : Fin 3) 2) 0 = v 0 := by
    show v (Equiv.swap (1 : Fin 3) 2 0) = v 0
    congr 1
  have h_tail_swap :
      Fin.tail (v ∘ Equiv.swap (1 : Fin 3) 2) = ![v 2, v 1] := by
    funext i
    fin_cases i
    · show v (Equiv.swap (1 : Fin 3) 2 1) = ![v 2, v 1] 0
      rw [Equiv.swap_apply_left, Matrix.cons_val_zero]
    · show v (Equiv.swap (1 : Fin 3) 2 2) = ![v 2, v 1] 1
      rw [Equiv.swap_apply_right]
      rfl
  have h_tail_v : Fin.tail v = ![v 1, v 2] := by
    funext i
    fin_cases i <;> rfl
  rw [h_swap_0, h_tail_swap, h_tail_v]
  -- Goal: `fderivWithin (D²f) s x (v 0) ![v 2, v 1]`
  --     = `fderivWithin (D²f) s x (v 0) ![v 1, v 2]`.
  -- Strategy: both sides equal `fderivWithin (φ_bc/φ_cb) s x (v 0)` via chain
  -- rule, and `φ_bc = φ_cb` on `s` by pointwise symmetry.
  set evalBC : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) ℝ →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => V) ℝ ![v 1, v 2]
    with hevalBC_def
  set evalCB : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) ℝ →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => V) ℝ ![v 2, v 1]
    with hevalCB_def
  set φ_bc : V → ℝ := fun y => iteratedFDerivWithin ℝ 2 f s y ![v 1, v 2]
    with hφ_bc_def
  set φ_cb : V → ℝ := fun y => iteratedFDerivWithin ℝ 2 f s y ![v 2, v 1]
    with hφ_cb_def
  have hφ_eq : Set.EqOn φ_bc φ_cb s := fun y hy =>
    iteratedFDerivWithin_two_swap hs_open hf hy (v 1) (v 2)
  -- Chain rule: HasFDerivWithinAt φ_bc (evalBC ∘L ...) s x.
  have h_D2_has :
      HasFDerivWithinAt (iteratedFDerivWithin ℝ 2 f s)
        (fderivWithin ℝ (iteratedFDerivWithin ℝ 2 f s) s x) s x :=
    h_D2_diff.hasFDerivWithinAt
  have h_φ_bc :
      HasFDerivWithinAt φ_bc
        (evalBC.comp (fderivWithin ℝ (iteratedFDerivWithin ℝ 2 f s) s x)) s x :=
    evalBC.hasFDerivAt.comp_hasFDerivWithinAt x h_D2_has
  have h_φ_cb :
      HasFDerivWithinAt φ_cb
        (evalCB.comp (fderivWithin ℝ (iteratedFDerivWithin ℝ 2 f s) s x)) s x :=
    evalCB.hasFDerivAt.comp_hasFDerivWithinAt x h_D2_has
  -- `φ_bc = φ_cb` on `s`, so `φ_bc` also has the `evalCB ∘L …` derivative.
  have h_φ_bc' :
      HasFDerivWithinAt φ_bc
        (evalCB.comp (fderivWithin ℝ (iteratedFDerivWithin ℝ 2 f s) s x)) s x :=
    h_φ_cb.congr (fun y hy => hφ_eq hy) (hφ_eq hx)
  -- Uniqueness of fderivWithin ⟹ the two derivative CLMs are equal.
  have h_eq : evalBC.comp (fderivWithin ℝ (iteratedFDerivWithin ℝ 2 f s) s x)
            = evalCB.comp (fderivWithin ℝ (iteratedFDerivWithin ℝ 2 f s) s x) :=
    h_unique_at_x.eq h_φ_bc h_φ_bc'
  -- Apply both CLMs to `v 0` to extract the scalar equality.
  have h_apply := ContinuousLinearMap.ext_iff.mp h_eq (v 0)
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, hevalBC_def,
    hevalCB_def, ContinuousMultilinearMap.apply_apply] at h_apply
  exact h_apply.symm

/-- First-two-slot swap of `D³f(x)` (the transposition `(0 1)`).

Unfolding via `iteratedFDerivWithin_succ_apply_right` reduces this to
the symmetry of `D²(∇f)(x)` in its two slots — exactly the content
of `iteratedFDerivWithin_two_fderiv_swap` (since `∇f` is `C²` when
`f` is `C³`). -/
private lemma iteratedFDerivWithin_three_swap_first_two
    (hs_open : IsOpen s) (hf : ContDiffOn ℝ 3 f s)
    {x : V} (hx : x ∈ s) (v : Fin 3 → V) :
    iteratedFDerivWithin ℝ 3 f s x (v ∘ Equiv.swap (0 : Fin 3) 1)
      = iteratedFDerivWithin ℝ 3 f s x v := by
  have hs_unique : UniqueDiffOn ℝ s := hs_open.uniqueDiffOn
  have h_apply_l :=
    iteratedFDerivWithin_succ_apply_right (𝕜 := ℝ) (n := 2) (f := f) (s := s)
      (x := x) hs_unique hx (v ∘ Equiv.swap (0 : Fin 3) 1)
  have h_apply_r :=
    iteratedFDerivWithin_succ_apply_right (𝕜 := ℝ) (n := 2) (f := f) (s := s)
      (x := x) hs_unique hx v
  -- The lemma is stated for `(n+1)` but `2+1` is defeq to `3`, so we can
  -- transport these equalities along `rfl`.
  rw [show iteratedFDerivWithin ℝ 3 f s x (v ∘ Equiv.swap (0 : Fin 3) 1)
       = iteratedFDerivWithin ℝ 2 (fderivWithin ℝ f s) s x
           (Fin.init (v ∘ Equiv.swap (0 : Fin 3) 1))
           ((v ∘ Equiv.swap (0 : Fin 3) 1) (Fin.last 2)) from h_apply_l]
  rw [show iteratedFDerivWithin ℝ 3 f s x v
       = iteratedFDerivWithin ℝ 2 (fderivWithin ℝ f s) s x
           (Fin.init v) (v (Fin.last 2)) from h_apply_r]
  -- Compute last and init for `v ∘ swap 0 1` and `v`.
  have h_last_swap :
      (v ∘ Equiv.swap (0 : Fin 3) 1) (Fin.last 2) = v (Fin.last 2) := by
    show v (Equiv.swap (0 : Fin 3) 1 (Fin.last 2)) = v (Fin.last 2)
    congr 1
  have h_init_swap :
      Fin.init (v ∘ Equiv.swap (0 : Fin 3) 1) = ![v 1, v 0] := by
    funext i
    fin_cases i
    · show v (Equiv.swap (0 : Fin 3) 1 0) = ![v 1, v 0] 0
      rw [Equiv.swap_apply_left, Matrix.cons_val_zero]
    · show v (Equiv.swap (0 : Fin 3) 1 1) = ![v 1, v 0] 1
      rw [Equiv.swap_apply_right]
      rfl
  have h_init_v : Fin.init v = ![v 0, v 1] := by
    funext i; fin_cases i <;> rfl
  rw [h_last_swap, h_init_swap, h_init_v]
  -- Reduces to symmetry of `D²(∇f)(x)` in its two slots.
  congr 1
  exact iteratedFDerivWithin_two_fderiv_swap hs_open hf hx (v 1) (v 0)

/-- **Symmetry of the third iterated derivative on an open set.** For
a real-valued `C³` function on an open set `s ⊆ V`, the third
iterated derivative at any `x ∈ s` is invariant under every
permutation of its arguments — i.e., it is a symmetric trilinear
form. -/
theorem iteratedFDerivWithin_three_isSymm
    (hs_open : IsOpen s) (hf : ContDiffOn ℝ 3 f s)
    {x : V} (hx : x ∈ s) :
    IsSymm (iteratedFDerivWithin ℝ 3 f s x) := by
  have h_swap_01 := iteratedFDerivWithin_three_swap_first_two hs_open hf hx
  have h_swap_12 := iteratedFDerivWithin_three_swap_last_two hs_open hf hx
  -- Derive swap (0 2) via `(0 2) = (0 1)·(1 2)·(0 1)` in `S₃`.
  have h_swap_02 : ∀ v : Fin 3 → V,
      iteratedFDerivWithin ℝ 3 f s x (v ∘ Equiv.swap (0 : Fin 3) 2)
        = iteratedFDerivWithin ℝ 3 f s x v := by
    intro v
    have h_decomp : (Equiv.swap (0 : Fin 3) 2 : Equiv.Perm (Fin 3))
        = Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2 *
            Equiv.swap (0 : Fin 3) 1 := by
      ext i; fin_cases i <;> rfl
    have h_decomp_fn :
        v ∘ (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2 *
              Equiv.swap (0 : Fin 3) 1)
        = ((v ∘ Equiv.swap (0 : Fin 3) 1) ∘ Equiv.swap (1 : Fin 3) 2) ∘
            Equiv.swap (0 : Fin 3) 1 := by
      funext i
      simp [Function.comp, Equiv.Perm.mul_apply]
    rw [h_decomp, h_decomp_fn,
      h_swap_01 ((v ∘ Equiv.swap (0 : Fin 3) 1) ∘ Equiv.swap (1 : Fin 3) 2),
      h_swap_12 (v ∘ Equiv.swap (0 : Fin 3) 1),
      h_swap_01 v]
  -- Single-swap symmetry for any transposition in `Fin 3`.
  have h_swap_any : ∀ (v : Fin 3 → V) (a b : Fin 3), a ≠ b →
      iteratedFDerivWithin ℝ 3 f s x (v ∘ Equiv.swap a b)
        = iteratedFDerivWithin ℝ 3 f s x v := by
    intro v a b hab
    fin_cases a <;> fin_cases b <;>
      first
      | exact (hab rfl).elim
      | exact h_swap_01 v
      | exact h_swap_02 v
      | exact h_swap_12 v
      | (rw [Equiv.swap_comm]; first
         | exact h_swap_01 v
         | exact h_swap_02 v
         | exact h_swap_12 v)
  -- Extend to all of `S₃` via `swap_induction_on`.
  suffices h : ∀ (σ : Equiv.Perm (Fin 3)) (v : Fin 3 → V),
      iteratedFDerivWithin ℝ 3 f s x (v ∘ σ)
        = iteratedFDerivWithin ℝ 3 f s x v by
    intro v σ; exact h σ v
  intro σ
  induction σ using Equiv.Perm.swap_induction_on with
  | one =>
    intro v
    show iteratedFDerivWithin ℝ 3 f s x (v ∘ (1 : Equiv.Perm (Fin 3)))
         = iteratedFDerivWithin ℝ 3 f s x v
    rfl
  | swap_mul τ a b hab ih =>
    intro v
    have hcomp : v ∘ (Equiv.swap a b * τ) = (v ∘ Equiv.swap a b) ∘ τ := by
      funext i; rfl
    rw [hcomp, ih (v ∘ Equiv.swap a b)]
    exact h_swap_any v a b hab

end IteratedFDerivWithinSymm

/-- **Polarization principle for a symmetric multilinear form bounded
by a PSD bilinear form.**

Let `A` be a continuous symmetric `k`-linear form on `V` and `B` a
continuous bilinear form on `V` with `0 ≤ B[h, h]` for every `h`
(positive-semidefiniteness on the diagonal). If the diagonal of `A`
satisfies `|A[h, …, h]| ≤ α · (√B[h, h])^k` for every `h : V` and some
`α ≥ 0`, then for all `v : Fin k → V`,

  `|A v| ≤ α · ∏ᵢ √B[v i, v i]`.

**Proof outline.** First reduce to the strictly positive-definite
case by replacing `B` with `B + ε · ⟨·, ·⟩` and taking `ε → 0⁺`.
Working with `B` positive definite, the seminorm `‖h‖_B := √B[h, h]`
is a genuine norm; normalize each `vᵢ` to be of unit `B`-norm. The
diagonal bound then reads `|A[h, …, h]| ≤ α` on the unit ball, and
the standard polarization identity for symmetric `k`-linear forms,

  `k! · A[h₁, …, h_k] = ∑_{ε ∈ {0, 1}^k} (-1)^{k-Σεᵢ} A[Σ εᵢ hᵢ, …]`,

combined with rescaling each `vᵢ ↦ λᵢ vᵢ` and optimizing over
`λᵢ > 0`, yields the constant-`α` bound on the polarized form.
This is the Banach-style result that on a real inner-product space
the operator norm of a symmetric multilinear map equals the supremum
of its diagonal restricted to the unit ball. -/
theorem multilinear_polarization_of_diagonal_bound
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin k => V) ℝ)
    (B : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) ℝ)
    (_hA_symm : IsSymm A)
    (_hB_psd : ∀ h : V, 0 ≤ B ![h, h])
    (α : ℝ) (_hα_nn : 0 ≤ α)
    (_h_diag : ∀ h : V, |A (fun _ => h)| ≤ α * (Real.sqrt (B ![h, h])) ^ k)
    (v : Fin k → V) :
    |A v| ≤ α * ∏ i, Real.sqrt (B ![v i, v i]) := by
  sorry

/-- **Trilinear specialization** of `multilinear_polarization_of_diagonal_bound`
in the form directly consumed by `Irn.LHSCB.self_concordant_polarization`:
for `k = 3`, the product over `Fin 3` is expanded into an explicit
three-fold product `√B(·, a) · √B(·, b) · √B(·, c)`, with each
diagonal `B ![v, v]` re-expressed as `B (fun _ => v)` to match the
shape of `iteratedFDerivWithin ℝ 2 …`.

A thin wrapper around the general statement; the proof reduces to
`Fin.prod_univ_three` and rewriting `![v, v] = fun _ => v`. -/
theorem trilinear_polarization_of_diagonal_bound
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => V) ℝ)
    (B : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) ℝ)
    (hA_symm : IsSymm A)
    (hB_psd : ∀ h : V, 0 ≤ B (fun _ => h))
    (α : ℝ) (hα_nn : 0 ≤ α)
    (h_diag : ∀ h : V, |A (fun _ => h)| ≤
        α * (Real.sqrt (B (fun _ => h))) ^ 3)
    (a b c : V) :
    |A ![a, b, c]| ≤
      α * Real.sqrt (B (fun _ => a)) * Real.sqrt (B (fun _ => b)) *
        Real.sqrt (B (fun _ => c)) := by
  have hB_diag_eq : ∀ h : V, B ![h, h] = B (fun _ => h) := by
    intro h
    congr 1
    funext i
    fin_cases i <;> rfl
  have hB_psd' : ∀ h : V, 0 ≤ B ![h, h] := fun h => by
    rw [hB_diag_eq]; exact hB_psd h
  have h_diag' : ∀ h : V, |A (fun _ => h)| ≤ α * (Real.sqrt (B ![h, h])) ^ 3 := by
    intro h; rw [hB_diag_eq]; exact h_diag h
  have h_main := multilinear_polarization_of_diagonal_bound A B hA_symm hB_psd' α hα_nn
    h_diag' ![a, b, c]
  -- Expand the product over `Fin 3` and rewrite each diagonal.
  have h_prod_eq :
      ∏ i : Fin 3, Real.sqrt (B ![(![a, b, c] : Fin 3 → V) i,
        (![a, b, c] : Fin 3 → V) i])
      = Real.sqrt (B (fun _ => a)) * Real.sqrt (B (fun _ => b)) *
          Real.sqrt (B (fun _ => c)) := by
    rw [Fin.prod_univ_three]
    simp [hB_diag_eq]
  rw [h_prod_eq] at h_main
  -- The bound `α · (X · Y · Z)` from the abstract theorem matches the
  -- target `α · X · Y · Z` up to associativity.
  linarith [h_main]

end TrilinForm

end Irn
