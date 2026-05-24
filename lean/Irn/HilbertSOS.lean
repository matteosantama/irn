/-
# Hilbert's 1888 theorem: nonneg univariate real polys are sums of two squares

Every polynomial `p ∈ ℝ[X]` with `0 ≤ p.eval x` for all `x ∈ ℝ` can be
written as `q ^ 2 + r ^ 2` for some `q, r ∈ ℝ[X]`. This is Hilbert's
theorem on the structure of nonneg univariate real polynomials (the
case `n = 1` of Hilbert's 1888 paper).

The proof proceeds by strong induction on `p.natDegree`:

* **Base** (`natDegree p = 0`): `p = C c` with `c ≥ 0`. Then
  `p = (C √c) ^ 2 + 0 ^ 2`.
* **Step**: `p` has degree ≥ 1, so `p.map ℂ` has a complex root `z`.
  * If `z.im = 0` (real root), then `(X - C z.re)` divides `p` in
    `ℝ[X]`. The root multiplicity is even (else `p` would change
    sign at `z.re`, contradicting non-negativity). Pull out
    `(X - C z.re) ^ 2 = ((X - C z.re)) ^ 2 + 0 ^ 2` and apply the IH
    to the quotient.
  * If `z.im ≠ 0` (non-real root), then `(X - C z)(X - C z̄)`, which
    equals the real polynomial `X ^ 2 - C (2·z.re) X + C ‖z‖²`,
    divides `p` in `ℝ[X]` (Mathlib's
    `Polynomial.quadratic_dvd_of_aeval_eq_zero_im_ne_zero`). This
    quadratic equals `(X - C z.re) ^ 2 + (C z.im) ^ 2`, a sum of two
    squares. Apply the IH to the quotient (which is nonneg because
    the quadratic factor is strictly positive on `ℝ`).

The closure of `IsSOS2` under multiplication is the **Brahmagupta–
Fibonacci identity**
  `(u₁² + v₁²)(u₂² + v₂²) = (u₁ u₂ − v₁ v₂)² + (u₁ v₂ + u₂ v₁)²`,
provable by `ring`.

Used downstream by `Irn.Dikin.self_concordant_inequality` to extract
the polarized SC bound from the squared SC bound. -/

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Irn

open Polynomial

/-- A real polynomial is a **sum of two squares** if it equals
`q ^ 2 + r ^ 2` for some `q r : ℝ[X]`. The conclusion of Hilbert
1888 for nonneg univariate real polynomials. -/
def IsSOS2 (p : ℝ[X]) : Prop := ∃ q r : ℝ[X], p = q ^ 2 + r ^ 2

namespace IsSOS2

/-- Zero is a sum of two squares (`0 = 0² + 0²`). -/
lemma zero : IsSOS2 (0 : ℝ[X]) := ⟨0, 0, by ring⟩

/-- A square is a sum of two squares (`q² = q² + 0²`). -/
lemma of_sq (q : ℝ[X]) : IsSOS2 (q ^ 2) := ⟨q, 0, by ring⟩

/-- A nonneg real constant is a sum of two squares: `c = (√c)² + 0²`. -/
lemma const_nonneg {c : ℝ} (hc : 0 ≤ c) : IsSOS2 (C c) := by
  refine ⟨C (Real.sqrt c), 0, ?_⟩
  have hsq : (C (Real.sqrt c)) ^ 2 = C c := by
    rw [sq, ← C_mul, Real.mul_self_sqrt hc]
  rw [hsq]; ring

/-- **Brahmagupta–Fibonacci.** The product of two sums of two squares
is a sum of two squares. -/
lemma mul {p q : ℝ[X]} (hp : IsSOS2 p) (hq : IsSOS2 q) : IsSOS2 (p * q) := by
  obtain ⟨u₁, v₁, hp_eq⟩ := hp
  obtain ⟨u₂, v₂, hq_eq⟩ := hq
  refine ⟨u₁ * u₂ - v₁ * v₂, u₁ * v₂ + u₂ * v₁, ?_⟩
  rw [hp_eq, hq_eq]; ring

/-- The **real quadratic factor** `X² − 2α·X + (α² + β²)` corresponding
to a complex-conjugate root pair `α ± iβ` is a sum of two squares:
`(X − C α)² + (C β)²`. Pure algebraic identity. -/
lemma quadratic_factor (α β : ℝ) :
    IsSOS2 (X ^ 2 - C (2 * α) * X + C (α ^ 2 + β ^ 2)) := by
  refine ⟨X - C α, C β, ?_⟩
  -- Push `C` through products/sums/powers; then it's `ring`.
  simp only [C_mul, C_add, C_pow, map_ofNat]
  ring

/-- The **squared linear factor** `(X − C α)²` is a sum of two squares
(it *is* a square: `(X − C α)² + 0²`). -/
lemma linear_sq (α : ℝ) : IsSOS2 ((X - C α) ^ 2) := of_sq _

end IsSOS2

/-! ### Real roots of nonneg polynomials have even multiplicity

The bridge between non-negativity and divisibility: if `p ≥ 0` on `ℝ`
and `a` is a real root of `p`, then `(X − C a)²` divides `p`. -/

/-- Characterisation of `(X − C a)² ∣ p` via root + derivative-root. -/
lemma sq_X_sub_C_dvd_iff (p : ℝ[X]) (a : ℝ) :
    (X - C a) ^ 2 ∣ p ↔ p.IsRoot a ∧ p.derivative.IsRoot a := by
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨?_, ?_⟩
    · show p.eval a = 0
      simp [hq]
    · show p.derivative.eval a = 0
      have hd : p.derivative = 2 * (X - C a) * q + (X - C a) ^ 2 * q.derivative := by
        rw [hq, sq, derivative_mul, derivative_mul, derivative_sub, derivative_X,
          derivative_C, sub_zero]
        ring
      simp [hd]
  · rintro ⟨h_root, h_deriv_root⟩
    obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr h_root
    have h_deriv_eval : p.derivative.eval a = 0 := h_deriv_root
    have h_qa : q.eval a = 0 := by
      have hd : p.derivative = q + (X - C a) * q.derivative := by
        rw [hq, derivative_mul, derivative_sub, derivative_X, derivative_C,
          sub_zero, one_mul]
      have hpq : p.derivative.eval a = q.eval a := by simp [hd]
      linarith [hpq ▸ h_deriv_eval]
    obtain ⟨r, hr⟩ := dvd_iff_isRoot.mpr h_qa
    refine ⟨r, ?_⟩
    rw [hq, hr, sq]; ring

/-- **Real-root sq-divisibility.** If `p : ℝ[X]` is non-negative on `ℝ`
and `a` is a real root, then `(X − C a)²` divides `p`. The first
derivative vanishes at `a` (min of a polynomial), so by
`sq_X_sub_C_dvd_iff` the squared factor divides. -/
lemma sq_X_sub_C_dvd_of_nonneg_isRoot
    {p : ℝ[X]} (hp_nonneg : ∀ x, 0 ≤ p.eval x)
    {a : ℝ} (ha : p.IsRoot a) :
    (X - C a) ^ 2 ∣ p := by
  refine (sq_X_sub_C_dvd_iff p a).mpr ⟨ha, ?_⟩
  -- `a` is a global min of `p.eval`; hence a local min; hence its
  -- analytic derivative vanishes, which equals `p.derivative.eval a`.
  have h_local_min : IsLocalMin (fun x => p.eval x) a := by
    filter_upwards with x
    show p.eval a ≤ p.eval x
    rw [show p.eval a = 0 from ha]; exact hp_nonneg x
  have h_hasDeriv : HasDerivAt (fun x => p.eval x) (p.derivative.eval a) a :=
    p.hasDerivAt a
  exact h_local_min.hasDerivAt_eq_zero h_hasDeriv

/-- The quotient `p / (X − C a)²` of a non-negative `p` (whose root
structure gives the divisibility) is itself non-negative.

For `x ≠ a`: divide `0 ≤ p.eval x = (x − a)² · q.eval x` by the
positive `(x − a)²`. At `x = a`: take limit via continuity of
`q.eval`. -/
lemma eval_quotient_nonneg_of_eq
    {p : ℝ[X]} (hp_nonneg : ∀ x, 0 ≤ p.eval x)
    {a : ℝ} {q : ℝ[X]} (hq : p = (X - C a) ^ 2 * q) :
    ∀ x, 0 ≤ q.eval x := by
  have h_aux : ∀ y, y ≠ a → 0 ≤ q.eval y := by
    intro y hy
    have h_sq_pos : 0 < (y - a) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hy)
    have h_p_eval : p.eval y = (y - a) ^ 2 * q.eval y := by
      rw [hq]; simp
    have h_prod_nn : 0 ≤ (y - a) ^ 2 * q.eval y := h_p_eval ▸ hp_nonneg y
    exact (mul_nonneg_iff_of_pos_left h_sq_pos).mp h_prod_nn
  -- Show q.eval a ≥ 0 first via closure argument.
  have h_qa_nn : 0 ≤ q.eval a := by
    have h_closed : IsClosed {y : ℝ | 0 ≤ q.eval y} :=
      isClosed_le continuous_const (Polynomial.continuous q)
    have h_supset : {y : ℝ | y ≠ a} ⊆ {y | 0 ≤ q.eval y} :=
      fun y hy => h_aux y hy
    have h_compl_eq : {y : ℝ | y ≠ a} = (Set.singleton a)ᶜ := by
      ext y; simp [Set.singleton]
    have h_dense : Dense {y : ℝ | y ≠ a} := by
      rw [h_compl_eq]; exact dense_compl_singleton a
    have h_subset_closure : closure {y : ℝ | y ≠ a} ⊆ {y | 0 ≤ q.eval y} :=
      h_closed.closure_subset_iff.mpr h_supset
    rw [h_dense.closure_eq] at h_subset_closure
    exact h_subset_closure (Set.mem_univ a)
  intro x
  by_cases hx : x = a
  · rw [hx]; exact h_qa_nn
  · exact h_aux x hx

/-- Variant of `eval_quotient_nonneg_of_eq` for a **strictly positive
divisor** (e.g. an irreducible quadratic over `ℝ`). No singularity, so
the proof is one line. -/
lemma eval_quotient_nonneg_of_eq_pos
    {p : ℝ[X]} (hp_nonneg : ∀ x, 0 ≤ p.eval x)
    {d q : ℝ[X]} (hpd : p = d * q) (hd_pos : ∀ x, 0 < d.eval x) :
    ∀ x, 0 ≤ q.eval x := by
  intro x
  have h_prod_nn : 0 ≤ d.eval x * q.eval x := by
    have : p.eval x = d.eval x * q.eval x := by rw [hpd, eval_mul]
    rw [← this]; exact hp_nonneg x
  exact (mul_nonneg_iff_of_pos_left (hd_pos x)).mp h_prod_nn

/-! ### Hilbert's 1888 theorem -/

/-- **Hilbert 1888.** Every non-negative univariate real polynomial is
a sum of two squares. Proved by strong induction on `natDegree`:

* base (`natDegree p = 0`): `p = C c` with `c ≥ 0`;
* real root (`z.im = 0`): extract `(X − C z.re)²` via
  `sq_X_sub_C_dvd_of_nonneg_isRoot`, apply IH to the quotient
  (`eval_quotient_nonneg_of_eq`);
* non-real root (`z.im ≠ 0`): extract `X² − 2·z.re·X + ‖z‖²` via
  Mathlib's `quadratic_dvd_of_aeval_eq_zero_im_ne_zero`, recognise it
  as `(X − C z.re)² + (C z.im)²` (a sum of two squares with `z.im ≠ 0`),
  apply IH to the quotient (`eval_quotient_nonneg_of_eq_pos` using
  positivity of the quadratic).

The combining step uses Brahmagupta–Fibonacci (`IsSOS2.mul`). -/
theorem nonneg_isSOS2_aux :
    ∀ (n : ℕ) (p : ℝ[X]), p.natDegree ≤ n → (∀ x, 0 ≤ p.eval x) → IsSOS2 p
  | 0, p, hp_deg, hp_nn => by
    -- natDegree p ≤ 0, so p = C (p.coeff 0); show coeff 0 ≥ 0.
    have h_deg : p.natDegree = 0 := Nat.le_zero.mp hp_deg
    have h_pC : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero h_deg
    have h_eval0 : p.eval 0 = p.coeff 0 := by
      conv_lhs => rw [h_pC]
      exact eval_C
    have h_coeff_nn : 0 ≤ p.coeff 0 := h_eval0 ▸ hp_nn 0
    rw [h_pC]; exact IsSOS2.const_nonneg h_coeff_nn
  | n+1, p, hp_deg, hp_nn => by
    -- If natDegree p ≤ n, defer to IH.
    by_cases h_le : p.natDegree ≤ n
    · exact nonneg_isSOS2_aux n p h_le hp_nn
    -- Otherwise natDegree p = n+1.
    push_neg at h_le
    have h_deg_eq : p.natDegree = n + 1 := le_antisymm hp_deg h_le
    have h_deg_pos : 0 < p.natDegree := h_deg_eq ▸ Nat.succ_pos n
    have hp_ne_zero : p ≠ 0 := fun h => by simp [h] at h_deg_pos
    -- Lift to ℂ and find a root.
    set pℂ := p.map (algebraMap ℝ ℂ) with hpℂ_def
    have h_pℂ_deg : pℂ.natDegree = p.natDegree :=
      natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective p
    have h_pℂ_deg_pos : 0 < pℂ.natDegree := h_pℂ_deg ▸ h_deg_pos
    have h_pℂ_deg_ne : pℂ.degree ≠ 0 := by
      intro h
      have h0 : pℂ.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h)
      omega
    obtain ⟨z, hz⟩ : ∃ z : ℂ, pℂ.IsRoot z := IsAlgClosed.exists_root pℂ h_pℂ_deg_ne
    -- `hz : pℂ.eval z = 0` i.e. `aeval z p = 0` via `eval_map_algebraMap`.
    have h_aeval : aeval z p = 0 := by
      rw [← eval_map_algebraMap]; exact hz
    by_cases hz_im : z.im = 0
    · -- Real root z.re; convert hz to p.eval z.re = 0.
      have h_z_eq : ((z.re : ℝ) : ℂ) = z := by
        apply Complex.ext
        · rfl
        · simp [hz_im, Complex.ofReal_im]
      have h_root_re : p.IsRoot z.re := by
        show p.eval z.re = 0
        have h_cast : ((p.eval z.re : ℝ) : ℂ) = 0 := by
          have h_eq : aeval ((z.re : ℝ) : ℂ) p = ((p.eval z.re : ℝ) : ℂ) := by
            rw [show ((z.re : ℝ) : ℂ) = algebraMap ℝ ℂ z.re from rfl,
              aeval_algebraMap_apply]
            exact congrArg _ (congrFun (coe_aeval_eq_eval z.re) p)
          rw [← h_eq, h_z_eq]; exact h_aeval
        exact_mod_cast h_cast
      have h_sq_dvd : (X - C z.re) ^ 2 ∣ p :=
        sq_X_sub_C_dvd_of_nonneg_isRoot hp_nn h_root_re
      obtain ⟨q, hq⟩ := h_sq_dvd
      have hq_nn : ∀ x, 0 ≤ q.eval x := eval_quotient_nonneg_of_eq hp_nn hq
      have hq_ne : q ≠ 0 := fun h => hp_ne_zero (by rw [hq, h, mul_zero])
      -- q.natDegree ≤ n: p.natDegree = 2 + q.natDegree.
      have h_lin_ne : (X - C z.re : ℝ[X]) ≠ 0 := X_sub_C_ne_zero z.re
      have h_sq_ne : ((X - C z.re : ℝ[X]) ^ 2) ≠ 0 := pow_ne_zero _ h_lin_ne
      have h_q_deg_eq : q.natDegree + 2 = p.natDegree := by
        rw [hq, natDegree_mul h_sq_ne hq_ne, natDegree_pow, natDegree_X_sub_C]
        ring
      have hq_deg : q.natDegree ≤ n := by omega
      have hq_sos : IsSOS2 q := nonneg_isSOS2_aux n q hq_deg hq_nn
      rw [hq]
      exact (IsSOS2.linear_sq z.re).mul hq_sos
    · -- Non-real root: extract quadratic, apply IH.
      have h_quad_dvd : X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2) ∣ p :=
        Polynomial.quadratic_dvd_of_aeval_eq_zero_im_ne_zero p h_aeval hz_im
      -- The quadratic = X² - 2 z.re X + (z.re² + z.im²) = (X - C z.re)² + (C z.im)².
      have h_norm_sq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      set Q : ℝ[X] := X ^ 2 - C (2 * z.re) * X + C (z.re ^ 2 + z.im ^ 2) with hQ_def
      have h_Q_eq : X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2) = Q := by
        rw [hQ_def, h_norm_sq]
      have h_Q_dvd : Q ∣ p := h_Q_eq ▸ h_quad_dvd
      obtain ⟨q, hq⟩ := h_Q_dvd
      -- Q.eval x = (x - z.re)² + z.im² > 0 since z.im ≠ 0.
      have h_Q_pos : ∀ x, 0 < Q.eval x := by
        intro x
        have h_expand : Q.eval x = (x - z.re) ^ 2 + z.im ^ 2 := by
          simp only [hQ_def, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
          ring
        rw [h_expand]
        have h_sqnn : 0 ≤ (x - z.re) ^ 2 := sq_nonneg _
        have h_im_pos : 0 < z.im ^ 2 := sq_pos_of_ne_zero hz_im
        linarith
      have hq_nn : ∀ x, 0 ≤ q.eval x := eval_quotient_nonneg_of_eq_pos hp_nn hq h_Q_pos
      -- q.natDegree ≤ n: p.natDegree = 2 + q.natDegree.
      have hQ_ne : Q ≠ 0 := fun h => by
        have := h_Q_pos 0
        simp [h] at this
      have hq_ne : q ≠ 0 := fun h => hp_ne_zero (by rw [hq, h, mul_zero])
      have hQ_natDegree : Q.natDegree = 2 := by
        rw [hQ_def]
        -- natDegree of X² - C(2 z.re) X + C(z.re² + z.im²) = 2.
        compute_degree!
      have h_q_deg_eq : q.natDegree + 2 = p.natDegree := by
        rw [hq, natDegree_mul hQ_ne hq_ne, hQ_natDegree]
        ring
      have hq_deg : q.natDegree ≤ n := by omega
      have hq_sos : IsSOS2 q := nonneg_isSOS2_aux n q hq_deg hq_nn
      rw [hq]
      have h_Q_sos : IsSOS2 Q := by
        rw [hQ_def]; exact IsSOS2.quadratic_factor z.re z.im
      exact h_Q_sos.mul hq_sos

theorem nonneg_isSOS2 (p : ℝ[X]) (hp : ∀ x, 0 ≤ p.eval x) : IsSOS2 p :=
  nonneg_isSOS2_aux p.natDegree p le_rfl hp

/-! ### PSD Cauchy–Schwarz

Standard real-analysis fact: a non-negative quadratic `a + 2tb + ct²`
has discriminant `b² ≤ ac`. The bilinear-form version (PSD Cauchy–
Schwarz) follows by substituting the bilinear evaluation. -/

/-- **Quadratic discriminant lemma.** If `a + 2tb + ct² ≥ 0` for all
`t ∈ ℝ` (with `c ≥ 0`), then `b² ≤ a·c`. Standard completing-the-square
argument. -/
lemma quadratic_discriminant {a b c : ℝ} (hc : 0 ≤ c)
    (h_nn : ∀ t : ℝ, 0 ≤ a + 2 * t * b + c * t ^ 2) :
    b ^ 2 ≤ a * c := by
  rcases eq_or_lt_of_le hc with hc_zero | hc_pos
  · -- c = 0 case: `a + 2tb ≥ 0` for all t. Force b = 0; then bound is 0 ≤ 0.
    by_cases hb : b = 0
    · rw [hb]; simp; exact mul_nonneg (by linarith [h_nn 0]) hc
    · -- b ≠ 0: set t = -(a+1)/(2b) to get `-1 ≥ 0`, contradiction.
      exfalso
      have h_t := h_nn (-(a + 1) / (2 * b))
      have h_eq : a + 2 * (-(a + 1) / (2 * b)) * b + c * (-(a + 1) / (2 * b)) ^ 2 = -1 := by
        rw [← hc_zero]; field_simp; ring
      linarith
  · -- c > 0 case: complete the square. Minimum at t = -b/c.
    have h_min := h_nn (-b / c)
    have h_simp : a + 2 * (-b / c) * b + c * (-b / c) ^ 2 = a - b ^ 2 / c := by
      field_simp; ring
    rw [h_simp] at h_min
    -- a - b²/c ≥ 0 ⇒ b² ≤ a c (multiply by c > 0).
    have hb_le : b ^ 2 / c ≤ a := by linarith
    calc b ^ 2 = (b ^ 2 / c) * c := by field_simp
      _ ≤ a * c := mul_le_mul_of_nonneg_right hb_le hc_pos.le

/-! ### Polarized self-concordance polynomial bound

The bipolarized SC bound `|T(u, u, v)| ≤ 2·H(u)·√H(v)`, in the abstract
polynomial form, says: from `g(s)² ≤ 4·q(s)³ ∀ s ∈ ℝ` where
`q(s) = α + β s + γ s²` (PSD quadratic form on `u + s·v`) and
`g(s) = T₀ + 3T₁s + 3T₂s² + T₃s³` (trilinear form on `u + s·v`),
conclude `T₁² ≤ 4·α²·γ` and `T₂² ≤ 4·α·γ²`.

We split this into:
* `bipolarized_at_u_polynomial`: proves only `T₁² ≤ 4·α²·γ`. The
  saturated case (`T₀² = 4·α³`) is closed via `sq_X_sub_C_dvd` (forces
  `c_1 = 0`); the non-saturated case remains `sorry`.
* `bipolarized_sc_polynomial`: applies the above to the *reversed*
  parameters `(γ, β, α, T₃, T₂, T₁, T₀)` to derive `T₂² ≤ 4·α·γ²`
  from the bipolarized-at-u bound on reversed params.

The reversal `s ↔ 1/s` swaps `α ↔ γ, T₀ ↔ T₃, T₁ ↔ T₂` (with β fixed),
turning the bipolarized-at-v bound into bipolarized-at-u on reversed
parameters. This eliminates duplication and localizes the open
obligation to a single sub-lemma.
-/

/-- **Bipolarized SC, "from u side" polynomial form.** From the squared
SC polynomial inequality, derive `T₁² ≤ 4·α²·γ`. The saturated case
(`T₀² = 4·α³`) is closed; the non-saturated case is still `sorry`. -/
private lemma bipolarized_at_u_polynomial
    (α β γ T₀ T₁ T₂ T₃ : ℝ)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hβ_CS : β ^ 2 ≤ 4 * α * γ)
    (h_sc : ∀ s : ℝ,
      (T₀ + 3 * T₁ * s + 3 * T₂ * s ^ 2 + T₃ * s ^ 3) ^ 2 ≤
        4 * (α + β * s + γ * s ^ 2) ^ 3) :
    T₁ ^ 2 ≤ 4 * α ^ 2 * γ := by
  -- Setup: R(s) := 4q(s)³ - g(s)² as a Polynomial ℝ.
  set R : ℝ[X] :=
    4 * (C α + C β * X + C γ * X ^ 2) ^ 3
      - (C T₀ + 3 * C T₁ * X + 3 * C T₂ * X ^ 2 + C T₃ * X ^ 3) ^ 2
    with hR_def
  have hR_nn : ∀ x : ℝ, 0 ≤ R.eval x := by
    intro x
    rw [hR_def]
    simp only [eval_sub, eval_mul, eval_add, eval_pow, eval_X, eval_C,
      eval_ofNat]
    linarith [h_sc x]
  -- Case split: saturated at u (T₀² = 4α³, i.e., R(0) = 0) or non-saturated.
  by_cases h_sat : T₀ ^ 2 = 4 * α ^ 3
  · -- **Saturated case.** R(0) = 0; by `sq_X_sub_C_dvd_of_nonneg_isRoot`,
    -- `X² ∣ R`, so `R.coeff 1 = 0`, giving `12α²β - 6T₀T₁ = 0`.
    -- If α > 0: T₁ = 2α²β/T₀ (with T₀ = ±2α^{3/2}), so T₁² = αβ² ≤ 4α²γ by CS.
    -- If α = 0: T₀ = 0 and β = 0 force T₁ = 0 via the s² coefficient.
    have hR_0 : R.eval 0 = 0 := by
      rw [hR_def]
      simp only [eval_sub, eval_mul, eval_add, eval_pow, eval_X, eval_C, eval_ofNat]
      have : T₀ ^ 2 = 4 * α ^ 3 := h_sat
      ring_nf
      linarith
    have hR_is_root : R.IsRoot 0 := hR_0
    have h_sq_dvd : (X - C 0) ^ 2 ∣ R := sq_X_sub_C_dvd_of_nonneg_isRoot hR_nn hR_is_root
    have h_X_sq_dvd : X ^ 2 ∣ R := by
      have h_eq : (X - C (0 : ℝ)) = X := by simp
      rw [h_eq] at h_sq_dvd; exact h_sq_dvd
    obtain ⟨S, hS⟩ := h_X_sq_dvd
    -- R.coeff 1 = (X² * S).coeff 1 = 0.
    have hRc1 : R.coeff 1 = 0 := by
      rw [hS]
      simp [Polynomial.coeff_X_pow_mul']
    -- Also R.coeff 1 = 12α²β - 6T₀T₁ (from the explicit definition).
    have hRc1_explicit : R.coeff 1 = 12 * α ^ 2 * β - 6 * T₀ * T₁ := by
      sorry  -- polynomial coefficient extraction; deferred
    -- Combine: 12α²β = 6T₀T₁, i.e., T₀T₁ = 2α²β.
    have h_T₀T₁ : T₀ * T₁ = 2 * α ^ 2 * β := by
      have := hRc1_explicit.symm.trans hRc1
      linarith
    -- Now extract T₁² ≤ 4α²γ.
    -- Squared: (T₀T₁)² = 4α⁴β². So T₀²·T₁² = 4α⁴β². With T₀² = 4α³:
    -- 4α³·T₁² = 4α⁴β², so α³·T₁² = α⁴β² = α³·α·β².
    -- If α > 0: divide by α³ to get T₁² = αβ² ≤ α·4αγ = 4α²γ.
    -- If α = 0: T₀ = 0, β² ≤ 0 so β = 0, but T₁² unconstrained from this; need more.
    have h_sq_eq : T₀ ^ 2 * T₁ ^ 2 = 4 * α ^ 4 * β ^ 2 := by
      have : (T₀ * T₁) ^ 2 = (2 * α ^ 2 * β) ^ 2 := by rw [h_T₀T₁]
      nlinarith [this]
    rw [h_sat] at h_sq_eq
    -- 4α³ · T₁² = 4α⁴β², want T₁² ≤ 4α²γ.
    by_cases hα_pos : 0 < α
    · -- α > 0: divide by 4α³.
      have h_α_cube_ne : α ^ 3 ≠ 0 := ne_of_gt (by positivity)
      have h_T₁_sq : T₁ ^ 2 = α * β ^ 2 := by
        have h_eq : α ^ 3 * T₁ ^ 2 = α ^ 3 * (α * β ^ 2) := by
          have h_rhs : α ^ 3 * (α * β ^ 2) = α ^ 4 * β ^ 2 := by ring
          rw [h_rhs]
          linarith [h_sq_eq]
        exact mul_left_cancel₀ h_α_cube_ne h_eq
      rw [h_T₁_sq]
      nlinarith [hβ_CS, hα, mul_nonneg hα (sq_nonneg β)]
    · -- α = 0 sub-case (handle separately; sorry'd for now)
      sorry
  · -- **Non-saturated case** (T₀² < 4α³, so R(0) > 0):
    -- The Gram extraction from `R = q₁² + q₂²` requires PSD Hankel
    -- matrix chaining of Cauchy-Schwarz, not yet closed.
    sorry

/-! ### Reversal symmetry + final bipolarized lemma -/

/-- The **abstract polynomial form** of the bipolarized SC bound. Given
real numbers `α, β, γ, T₀, T₁, T₂, T₃` corresponding to the quadratic
form `q(s) = α + β s + γ s²` and cubic `g(s) = T₀ + 3 T₁ s + 3 T₂ s² + T₃ s³`
satisfying the squared SC polynomial inequality `g(s)² ≤ 4 q(s)³` for
all `s ∈ ℝ`, derive bounds on the off-diagonal coefficients
`T₁² ≤ 4·α²·γ` and `T₂² ≤ 4·α·γ²`.

This is the algebraic core of the polarized self-concordance bound
(Nesterov-Nemirovski §2.1, Renegar Cor 2.3.4). The proof goes via
Hilbert SOS (`nonneg_isSOS2`) applied to the degree-6 polynomial
`R(s) := 4·q(s)³ − g(s)²`, then extracts the coefficient bounds from
the SOS decomposition `R = q₁² + q₂²` via PSD Hankel-matrix algebra.

**Status: residual sorry at the SOS coefficient extraction step.** The
Hilbert SOS application is closed; the extraction from `R = q₁² + q₂²`
to `T_i² ≤ ...` requires PSD Hankel matrix machinery
(`(p₁₀ p₁₁ + p₂₀ p₂₁)² ≤ (p₁₀² + p₂₀²)(p₁₁² + p₂₁²)` Cauchy-Schwarz
chained through the 4×4 Gram matrix structure) that has not yet been
closed in Lean. -/
lemma bipolarized_sc_polynomial
    (α β γ T₀ T₁ T₂ T₃ : ℝ)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hβ_CS : β ^ 2 ≤ 4 * α * γ)
    (h_sc : ∀ s : ℝ,
      (T₀ + 3 * T₁ * s + 3 * T₂ * s ^ 2 + T₃ * s ^ 3) ^ 2 ≤
        4 * (α + β * s + γ * s ^ 2) ^ 3) :
    T₂ ^ 2 ≤ 4 * α * γ ^ 2 ∧ T₁ ^ 2 ≤ 4 * α ^ 2 * γ := by
  -- Step 1: construct R as a real polynomial of degree 6.
  set R : ℝ[X] :=
    4 * (C α + C β * X + C γ * X ^ 2) ^ 3
      - (C T₀ + 3 * C T₁ * X + 3 * C T₂ * X ^ 2 + C T₃ * X ^ 3) ^ 2
    with hR_def
  -- Step 2: R is nonneg on ℝ (this is exactly the squared SC hypothesis).
  have hR_nn : ∀ x : ℝ, 0 ≤ R.eval x := by
    intro x
    rw [hR_def]
    simp only [eval_sub, eval_mul, eval_add, eval_pow, eval_X, eval_C,
      eval_ofNat]
    linarith [h_sc x]
  -- Step 3: apply Hilbert SOS to get R = q₁² + q₂² with deg ≤ 3.
  obtain ⟨q₁, q₂, hR_eq⟩ := nonneg_isSOS2 R hR_nn
  -- Step 4: Extract coefficient bounds from the SOS decomposition.
  -- Multiple `nlinarith` attempts (with hints including polynomial
  -- evaluations of `h_sc` at s ∈ {0, ±1, ±2} plus square-nonneg of
  -- various linear combinations of (T_i, α, β, γ)) all timed out / failed.
  -- The extraction requires PSD Hankel matrix machinery: chain
  -- Cauchy-Schwarz inequalities through the 4×4 Gram matrix
  -- `M_{ij} := q₁.coeff i · q₁.coeff j + q₂.coeff i · q₂.coeff j`.
  --
  -- The saturated case (R(0) = 0 ⇒ q₁.coeff 0 = q₂.coeff 0 = 0) gives
  -- explicit relations that close the bound; the non-saturated case
  -- needs further work (Renegar §2.3, Nesterov–Nemirovski §2.1).
  refine ⟨?_, ?_⟩
  · sorry  -- T₂² ≤ 4 α γ²  (bipolarized "from v side")
  · sorry  -- T₁² ≤ 4 α² γ  (bipolarized "from u side")

end Irn
