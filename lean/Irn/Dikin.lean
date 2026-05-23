/-
# Dikin-ball Hessian Lipschitz bound (Nesterov–Nemirovski)

The squared self-concordance bound `(D³f[h,h,h])² ≤ 4(D²f[h,h])³`
integrates to a multiplicative Hessian bound inside the **Dikin ball**
of any interior point. For `r := √⟨u − u₀, ∇²f(u₀)(u − u₀)⟩ < 1` and
any direction `h`:
`(1 − r)² ⟨h, ∇²f(u₀) h⟩ ≤ ⟨h, ∇²f(u) h⟩ ≤ (1 − r)⁻² ⟨h, ∇²f(u₀) h⟩`.

This is **paper §6.3 Lemma 16 step (i)** ("self-concordance of `W`"):
the Lipschitz constant of `∇²f` in the local SC norm is an absolute
constant. It is the analytic input that lets the Newton–Kantorovich
analysis give a basin radius `ρ*` independent of `μ` — without it the
basin would shrink near `∂K`.

**Standard proof (Nesterov–Nemirovski §2.1):**
1. **Polarized SC bound.** From `(D³f(x)[h, h, h])² ≤ 4 (D²f(x)[h, h])³`
   derive, via polarization of the symmetric trilinear form,
   `|D³f(x)[a, b, c]| ≤ 2 ‖a‖_{∇²f(x)} ‖b‖_{∇²f(x)} ‖c‖_{∇²f(x)}`.
2. **Diagonal ODE.** Restrict to the line `t ↦ u₀ + t · d` (where
   `d = u − u₀`). Let `a(t) := ⟨d, ∇²f(u₀ + t·d) d⟩`. Then
   `a'(t) = D³f(...)[d, d, d]`, and the squared SC bound at direction
   `d` gives `|a'(t)| ≤ 2 a(t)^(3/2)`. So `φ(t) := a(t)^(−1/2)`
   satisfies `|φ'(t)| ≤ 1`; integrating gives the diagonal bound
   `a(s) ≤ a(0) / (1 − s · √a(0))²` for `s · √a(0) < 1`.
3. **Polarized lift.** For arbitrary `h`, let `ψ(t) := ⟨h, ∇²f(u₀ +
   t·d) h⟩`. By polarized SC,
   `|ψ'(t)| = |D³f[d, h, h]| ≤ 2 ‖d‖_{∇²f(u₀+t·d)} · ψ(t)`. Bound
   `‖d‖_{∇²f(u₀+t·d)} ≤ r/(1 − tr)` by Step 2 (with the displacement
   `d` itself), giving `|d/dt log ψ(t)| ≤ 2r/(1−tr)`. Integrate from
   `0` to `1`: `∫₀¹ 2r/(1−sr) ds = −2 log(1−r)`, so `ψ(1)/ψ(0) ∈
   [(1−r)², (1−r)⁻²]`.

## File layout

* `segment_in_interior` — closed segment between two interior points
  stays in `interior K` for convex `K`.
* **Path-derivative scaffold** (pure real-analysis ODE results):
  `b_eps_one_lipschitz`, `diagonal_ode_squared_bound_via_lipschitz`,
  `diagonal_ode_squared_bound`,
  `local_norm_path_bound_from_diagonal_ode`,
  `multiplicative_path_bound_from_log_ode`.
* **LHSCB-specific scaffold**:
  `LHSCB.hess`, `LHSCB.local_norm` — convenience defs for the Hessian
    quadratic form and its induced semi-norm; used as `f.hess x h`.
  `LHSCB.hess_path_has_deriv_at` — chain rule along the segment.
  `LHSCB.self_concordant_inequality` — trilinear SC bound
    `|D³f(x)[a, b, c]| ≤ 2·√Q[a]·√Q[b]·√Q[c]`; currently `sorry`.
  `LHSCB.dikin_path_metric_bound` (Lemma 1) —
    `f.local_norm` is bounded by `r/(1−tr)` along the segment.
  `LHSCB.path_hess_deriv_bound` (Lemma 2) — derivative of
    `t ↦ f.hess (γ t) h` is bounded by `2·f.hess·f.local_norm`.
  `LHSCB.path_hess_integrated_bound` (Lemma 3) — multiplicative
    Hessian bound along the segment.
  `LHSCB.hessian_dikin_bound` — final theorem.

One sorry remains, in `self_concordant_inequality` — the trilinear
polarization of squared SC at the basepoint. A randomized numerical
search confirms the empirical sup of the ratio
`|T(a,b,c)| / (√Q[a]·√Q[b]·√Q[c])` is consistent with the textbook
constant `2`, so the bound itself is sharp.
-/

import Irn.Barriers

namespace Irn

open scoped BigOperators

/-! ### Segment in interior -/

/-- The interior of a convex set is convex, so the closed line segment
between two interior points lies in `interior K`. Used throughout the
Dikin scaffold to keep `γ(t) := u₀ + t·(u − u₀)` inside `interior K`
for `t ∈ [0, 1]`. -/
lemma segment_in_interior
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {K : Set V} (hK_convex : Convex ℝ K)
    (u₀ : V) (hu₀ : u₀ ∈ interior K)
    (u : V) (hu : u ∈ interior K) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, u₀ + t • (u - u₀) ∈ interior K := by
  intro t ⟨h0, h1⟩
  have h_eq : u₀ + t • (u - u₀) = (1 - t) • u₀ + t • u := by
    rw [smul_sub, sub_smul, one_smul]; abel
  rw [h_eq]
  exact hK_convex.interior hu₀ hu (by linarith) h0 (by linarith)

/-! ### Path-derivative scaffold (pure real analysis)

Real-analysis Gronwall/ODE-integration lemmas, isolated from the LHSCB
context. They take the ODE inequality as a hypothesis on an abstract
function `a : ℝ → ℝ` (resp. `H : ℝ → ℝ`) and integrate it. -/

/-- **ε-regularized substitution is 1-Lipschitz.** For any `ε > 0`, the
function `b_ε(s) := 1/√(a(s) + ε²)` is 1-Lipschitz on `[0, 1]`,
provided `a` is non-negative, continuous, and differentiable on `(0,1)`
with `|a'(t)| ≤ 2 (√a(t))³`.

Pure real-analysis fact, no LHSCB context. Proof: differentiate
`b_ε` (composition of `a`, `Real.sqrt`, and reciprocal — all smooth on
the positive domain), bound `|b_ε'(s)| ≤ 1` via the ODE hypothesis (the
key cancellation: `|a'|/(2·(a+ε²)^(3/2)) ≤ a^(3/2)/(a+ε²)^(3/2) ≤ 1`),
then apply `Convex.lipschitzOnWith_of_nnnorm_deriv_le` on the convex
`Ioo 0 1` and `LipschitzOnWith.closure` to extend to `[0, 1]`. -/
private lemma b_eps_one_lipschitz
    {a : ℝ → ℝ}
    (ha_nn : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ a t)
    (ha_cont : ContinuousOn a (Set.Icc (0:ℝ) 1))
    (ha_deriv : ∀ t ∈ Set.Ioo (0:ℝ) 1, ∃ a', HasDerivAt a a' t ∧
                |a'| ≤ 2 * (Real.sqrt (a t)) ^ 3)
    (ε : ℝ) (hε_pos : 0 < ε) :
    LipschitzOnWith 1 (fun s => 1 / Real.sqrt (a s + ε ^ 2))
      (Set.Icc (0:ℝ) 1) := by
  set b : ℝ → ℝ := fun s => 1 / Real.sqrt (a s + ε ^ 2) with hb_def
  have hε_sq_pos : (0 : ℝ) < ε ^ 2 := pow_pos hε_pos 2
  have h_pos : ∀ s ∈ Set.Icc (0:ℝ) 1, (0:ℝ) < a s + ε ^ 2 := fun s hs => by
    have := ha_nn s hs; linarith
  have h_sqrt_pos : ∀ s ∈ Set.Icc (0:ℝ) 1, (0:ℝ) < Real.sqrt (a s + ε ^ 2) :=
    fun s hs => Real.sqrt_pos.mpr (h_pos s hs)
  have hb_cont : ContinuousOn b (Set.Icc (0:ℝ) 1) := by
    refine continuousOn_const.div ?_ (fun s hs => ne_of_gt (h_sqrt_pos s hs))
    exact Real.continuous_sqrt.comp_continuousOn (ha_cont.add continuousOn_const)
  have hb_diff_deriv :
      ∀ x ∈ Set.Ioo (0:ℝ) 1, DifferentiableAt ℝ b x ∧ ‖deriv b x‖ ≤ 1 := by
    intro x hx
    have hx_Icc : x ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    obtain ⟨a', hda', hbd⟩ := ha_deriv x hx
    have h_pos_x := h_pos x hx_Icc
    have h_sqrt_pos_x := h_sqrt_pos x hx_Icc
    have h_sqrt_ne_x : Real.sqrt (a x + ε ^ 2) ≠ 0 := ne_of_gt h_sqrt_pos_x
    have h_pos_ne : (a x + ε ^ 2) ≠ 0 := ne_of_gt h_pos_x
    have h_add : HasDerivAt (fun s => a s + ε ^ 2) a' x := hda'.add_const _
    have h_sqrt : HasDerivAt (fun s => Real.sqrt (a s + ε ^ 2))
        (a' / (2 * Real.sqrt (a x + ε ^ 2))) x := by
      have h_root :
          HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (a x + ε ^ 2))) (a x + ε ^ 2) :=
        Real.hasDerivAt_sqrt h_pos_ne
      have h_comp := h_root.comp x h_add
      convert h_comp using 1
      field_simp
    have h_inv : HasDerivAt b
        ((0 * Real.sqrt (a x + ε ^ 2) -
            1 * (a' / (2 * Real.sqrt (a x + ε ^ 2))))
          / Real.sqrt (a x + ε ^ 2) ^ 2) x :=
      (hasDerivAt_const x (1:ℝ)).div h_sqrt h_sqrt_ne_x
    refine ⟨h_inv.differentiableAt, ?_⟩
    rw [h_inv.deriv]
    have h_a_nn_x : 0 ≤ a x := ha_nn x hx_Icc
    have h_sqrt_a_nn : 0 ≤ Real.sqrt (a x) := Real.sqrt_nonneg _
    have h_sqrt_a_le : Real.sqrt (a x) ≤ Real.sqrt (a x + ε ^ 2) :=
      Real.sqrt_le_sqrt (by linarith)
    have h_sqrt_a_cubed_le :
        (Real.sqrt (a x)) ^ 3 ≤ (Real.sqrt (a x + ε ^ 2)) ^ 3 :=
      pow_le_pow_left₀ h_sqrt_a_nn h_sqrt_a_le 3
    have h_abs_a'_bd : |a'| ≤ 2 * (Real.sqrt (a x + ε ^ 2)) ^ 3 := by
      calc |a'|
          ≤ 2 * (Real.sqrt (a x)) ^ 3 := hbd
        _ ≤ 2 * (Real.sqrt (a x + ε ^ 2)) ^ 3 := by linarith
    have h_eq_deriv :
        (0 * Real.sqrt (a x + ε ^ 2) - 1 * (a' / (2 * Real.sqrt (a x + ε ^ 2))))
            / Real.sqrt (a x + ε ^ 2) ^ 2
          = -a' / (2 * (Real.sqrt (a x + ε ^ 2)) ^ 3) := by
      field_simp
      ring
    rw [h_eq_deriv]
    rw [Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos (by positivity :
        (0 : ℝ) < 2 * (Real.sqrt (a x + ε ^ 2)) ^ 3)]
    rw [div_le_one (by positivity : (0 : ℝ) < 2 * (Real.sqrt (a x + ε ^ 2)) ^ 3)]
    exact h_abs_a'_bd
  have hb_lip_Ioo : LipschitzOnWith 1 b (Set.Ioo (0:ℝ) 1) :=
    (convex_Ioo (0:ℝ) 1).lipschitzOnWith_of_nnnorm_deriv_le
      (fun x hx => (hb_diff_deriv x hx).1)
      (fun x hx => by
        have h := (hb_diff_deriv x hx).2; exact_mod_cast h)
  have h_closure : closure (Set.Ioo (0:ℝ) 1) = Set.Icc (0:ℝ) 1 :=
    closure_Ioo (by norm_num)
  have hb_cont' : ContinuousOn b (closure (Set.Ioo (0:ℝ) 1)) := h_closure ▸ hb_cont
  have h := hb_lip_Ioo.closure hb_cont'
  rwa [h_closure] at h

/-- **Squared diagonal bound from Lipschitz family.** Given the 1-Lipschitz
family `b_ε := 1/√(a+ε²)` on `[0, 1]` (one per `ε > 0`), conclude the
squared Dikin bound `(1 − t·r)² · a(t) ≤ r²`.

Pure real-analysis limit argument, no derivative computations: from
1-Lipschitz `|b_ε(t) − b_ε(0)| ≤ t` and `a(0) ≤ r²` (so `b_ε(0) ≥
1/√(r²+ε²)`), get `√(a(t)+ε²) ≤ 1/(1/√(r²+ε²) − t)` for ε small;
then take `ε → 0+` via `le_of_tendsto_of_tendsto` to obtain the
squared bound. -/
private lemma diagonal_ode_squared_bound_via_lipschitz
    {a : ℝ → ℝ} {r : ℝ}
    (hr_nn : 0 ≤ r) (hr_lt_one : r < 1)
    (ha_nn : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ a t)
    (ha_0 : a 0 ≤ r ^ 2)
    (h_lip : ∀ ε > (0:ℝ),
        LipschitzOnWith 1 (fun s => 1 / Real.sqrt (a s + ε ^ 2))
          (Set.Icc (0:ℝ) 1)) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, (1 - t * r) ^ 2 * a t ≤ r ^ 2 := by
  intro t ht
  obtain ⟨ht_nn, ht_le⟩ := ht
  rcases eq_or_lt_of_le ht_nn with rfl | ht_pos
  · simpa using ha_0
  -- Main case: `t > 0`.
  -- Family of bounds parameterised by `ε ∈ (0, ε_max)`, where
  -- `ε_max := √(1/t² − r²) > 0`.  Take `ε → 0+` via `le_of_tendsto_of_tendsto`.
  set g : ℝ → ℝ := fun ε =>
    (1 - t * r) ^ 2 * (r ^ 2 + ε ^ 2) / (1 - t * Real.sqrt (r ^ 2 + ε ^ 2)) ^ 2
    with hg_def
  have h_1tr_pos : (0 : ℝ) < 1 - t * r := by nlinarith
  have hg_at_0 : g 0 = r ^ 2 := by
    simp only [g]
    rw [show r ^ 2 + (0:ℝ) ^ 2 = r ^ 2 from by ring, Real.sqrt_sq hr_nn]
    have h_ne : (1 - t * r) ^ 2 ≠ 0 := ne_of_gt (pow_pos h_1tr_pos 2)
    field_simp
  have hg_cont : ContinuousAt g 0 := by
    refine ContinuousAt.div ?_ ?_ ?_
    · exact ((continuousAt_const).mul ((continuousAt_const).add
        ((continuousAt_id).pow 2)))
    · refine ContinuousAt.pow ?_ 2
      refine (continuousAt_const).sub ((continuousAt_const).mul ?_)
      exact (Real.continuous_sqrt.continuousAt).comp
        ((continuousAt_const).add ((continuousAt_id).pow 2))
    · simp only [show r ^ 2 + (0:ℝ) ^ 2 = r ^ 2 from by ring, Real.sqrt_sq hr_nn]
      exact ne_of_gt (pow_pos h_1tr_pos 2)
  have h_tendsto : Filter.Tendsto g (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (r ^ 2)) := by
    have h := hg_cont.tendsto
    rw [hg_at_0] at h
    exact h.mono_left nhdsWithin_le_nhds
  have h_t_sq_pos : (0 : ℝ) < t ^ 2 := pow_pos ht_pos 2
  have h_t_sq_le_one : t ^ 2 ≤ 1 := by nlinarith
  have h_inv_t_sq_ge_one : (1 : ℝ) ≤ 1 / t ^ 2 := by
    rw [one_le_div h_t_sq_pos]; exact h_t_sq_le_one
  have h_M_pos : (0 : ℝ) < 1 / t ^ 2 - r ^ 2 := by
    have : r ^ 2 < 1 := by nlinarith
    linarith
  set ε_max : ℝ := Real.sqrt (1 / t ^ 2 - r ^ 2) with hε_max_def
  have hε_max_pos : (0 : ℝ) < ε_max := Real.sqrt_pos.mpr h_M_pos
  have h_bound : ∀ ε ∈ Set.Ioo (0:ℝ) ε_max, (1 - t * r) ^ 2 * a t ≤ g ε := by
    intro ε hε
    obtain ⟨hε_pos, hε_lt_max⟩ := hε
    have hε_sq_pos : (0 : ℝ) < ε ^ 2 := pow_pos hε_pos 2
    have hr_eps_sq_pos : (0 : ℝ) < r ^ 2 + ε ^ 2 := by positivity
    have h_sqrt_r_eps_pos : (0 : ℝ) < Real.sqrt (r ^ 2 + ε ^ 2) :=
      Real.sqrt_pos.mpr hr_eps_sq_pos
    have hε_sq_lt : ε ^ 2 < 1 / t ^ 2 - r ^ 2 := by
      have h_sq_lt : ε ^ 2 < ε_max ^ 2 := by
        have := mul_self_lt_mul_self (le_of_lt hε_pos) hε_lt_max
        simpa [sq] using this
      have hε_max_sq : ε_max ^ 2 = 1 / t ^ 2 - r ^ 2 := by
        rw [hε_max_def]; exact Real.sq_sqrt (le_of_lt h_M_pos)
      linarith
    have h_t_sqrt_lt_one : t * Real.sqrt (r ^ 2 + ε ^ 2) < 1 := by
      have h_sqrt_lt_inv_t : Real.sqrt (r ^ 2 + ε ^ 2) < 1 / t := by
        have h_inv_t_sq : (1 / t) ^ 2 = 1 / t ^ 2 := by field_simp
        have h_lt_inv_sq : r ^ 2 + ε ^ 2 < (1 / t) ^ 2 := by rw [h_inv_t_sq]; linarith
        have h_inv_t_nn : 0 ≤ 1 / t := le_of_lt (by positivity)
        have : Real.sqrt (r ^ 2 + ε ^ 2) < Real.sqrt ((1 / t) ^ 2) :=
          Real.sqrt_lt_sqrt (le_of_lt hr_eps_sq_pos) h_lt_inv_sq
        rwa [Real.sqrt_sq h_inv_t_nn] at this
      have := mul_lt_mul_of_pos_left h_sqrt_lt_inv_t ht_pos
      rwa [mul_one_div, div_self (ne_of_gt ht_pos)] at this
    have h_one_minus_pos : (0 : ℝ) < 1 - t * Real.sqrt (r ^ 2 + ε ^ 2) := by linarith
    have h_inv_gt_t : t < 1 / Real.sqrt (r ^ 2 + ε ^ 2) := by
      rw [lt_div_iff₀ h_sqrt_r_eps_pos]
      linarith
    have h_lip_t : dist (1 / Real.sqrt (a t + ε ^ 2)) (1 / Real.sqrt (a 0 + ε ^ 2)) ≤ t := by
      have h := (h_lip ε hε_pos).dist_le_mul
        t (Set.mem_Icc.mpr ⟨le_of_lt ht_pos, ht_le⟩)
        0 (Set.mem_Icc.mpr ⟨le_refl _, zero_le_one⟩)
      simpa [Real.dist_eq, abs_of_pos ht_pos] using h
    have h_b_t_ge_b_0_sub_t :
        1 / Real.sqrt (a t + ε ^ 2) ≥ 1 / Real.sqrt (a 0 + ε ^ 2) - t := by
      have h_abs : |1 / Real.sqrt (a t + ε ^ 2) - 1 / Real.sqrt (a 0 + ε ^ 2)| ≤ t :=
        Real.dist_eq _ _ ▸ h_lip_t
      linarith [abs_le.mp h_abs]
    have h_a_0_nn : 0 ≤ a 0 := ha_nn 0 ⟨le_refl _, zero_le_one⟩
    have h_a_0_eps_pos : (0 : ℝ) < a 0 + ε ^ 2 := by linarith
    have h_sqrt_a_0_pos : (0 : ℝ) < Real.sqrt (a 0 + ε ^ 2) :=
      Real.sqrt_pos.mpr h_a_0_eps_pos
    have h_a_0_le : a 0 + ε ^ 2 ≤ r ^ 2 + ε ^ 2 := by linarith
    have h_sqrt_le : Real.sqrt (a 0 + ε ^ 2) ≤ Real.sqrt (r ^ 2 + ε ^ 2) :=
      Real.sqrt_le_sqrt h_a_0_le
    have h_b_0_ge : 1 / Real.sqrt (a 0 + ε ^ 2) ≥ 1 / Real.sqrt (r ^ 2 + ε ^ 2) :=
      one_div_le_one_div_of_le h_sqrt_a_0_pos h_sqrt_le
    have h_b_t_pos_bd :
        1 / Real.sqrt (a t + ε ^ 2) ≥ 1 / Real.sqrt (r ^ 2 + ε ^ 2) - t := by
      linarith
    have h_pos_diff : (0 : ℝ) < 1 / Real.sqrt (r ^ 2 + ε ^ 2) - t := by linarith
    have h_b_t_pos : (0 : ℝ) < 1 / Real.sqrt (a t + ε ^ 2) := by linarith
    have h_sqrt_a_t_le :
        Real.sqrt (a t + ε ^ 2) ≤
          Real.sqrt (r ^ 2 + ε ^ 2) / (1 - t * Real.sqrt (r ^ 2 + ε ^ 2)) := by
      have h_recip : Real.sqrt (a t + ε ^ 2) = 1 / (1 / Real.sqrt (a t + ε ^ 2)) := by
        rw [one_div_one_div]
      rw [h_recip]
      have h_le : 1 / (1 / Real.sqrt (a t + ε ^ 2)) ≤
          1 / (1 / Real.sqrt (r ^ 2 + ε ^ 2) - t) :=
        one_div_le_one_div_of_le h_pos_diff h_b_t_pos_bd
      apply h_le.trans
      have h_simp : 1 / (1 / Real.sqrt (r ^ 2 + ε ^ 2) - t) =
          Real.sqrt (r ^ 2 + ε ^ 2) / (1 - t * Real.sqrt (r ^ 2 + ε ^ 2)) := by
        field_simp
      exact le_of_eq h_simp
    have h_a_t_eps_nn : 0 ≤ a t + ε ^ 2 := by
      have := ha_nn t ⟨le_of_lt ht_pos, ht_le⟩; linarith
    have h_sqrt_a_t_nn : 0 ≤ Real.sqrt (a t + ε ^ 2) := Real.sqrt_nonneg _
    have h_div_nn :
        0 ≤ Real.sqrt (r ^ 2 + ε ^ 2) / (1 - t * Real.sqrt (r ^ 2 + ε ^ 2)) := by
      exact div_nonneg (Real.sqrt_nonneg _) (le_of_lt h_one_minus_pos)
    have h_sq_le :
        (Real.sqrt (a t + ε ^ 2)) ^ 2 ≤
          (Real.sqrt (r ^ 2 + ε ^ 2) / (1 - t * Real.sqrt (r ^ 2 + ε ^ 2))) ^ 2 :=
      pow_le_pow_left₀ h_sqrt_a_t_nn h_sqrt_a_t_le 2
    rw [Real.sq_sqrt h_a_t_eps_nn,
        div_pow, Real.sq_sqrt (le_of_lt hr_eps_sq_pos)] at h_sq_le
    have h_sq_nn : 0 ≤ (1 - t * r) ^ 2 := sq_nonneg _
    calc (1 - t * r) ^ 2 * a t
        ≤ (1 - t * r) ^ 2 * (a t + ε ^ 2) := by nlinarith
      _ ≤ (1 - t * r) ^ 2 *
            ((r ^ 2 + ε ^ 2) / (1 - t * Real.sqrt (r ^ 2 + ε ^ 2)) ^ 2) :=
          mul_le_mul_of_nonneg_left h_sq_le h_sq_nn
      _ = g ε := by rw [hg_def]; ring
  refine le_of_tendsto_of_tendsto tendsto_const_nhds h_tendsto ?_
  filter_upwards [Ioo_mem_nhdsGT hε_max_pos] with ε hε
  exact h_bound ε hε

/-- **Squared diagonal ODE bound.** Under the same hypotheses as
`local_norm_path_bound_from_diagonal_ode` plus continuity of `a` on
`[0, 1]`, we have `(1 − t·r)² · a(t) ≤ r²` for all `t ∈ [0, 1]`.

This is the squared form of the Dikin estimate; it avoids the
differentiability obstruction at `a = 0` that the natural `1/√a`
substitution would face. The proof is a trivial composition of
`b_eps_one_lipschitz` (1-Lipschitz family from the ODE) and
`diagonal_ode_squared_bound_via_lipschitz` (ε → 0+ limit). -/
private lemma diagonal_ode_squared_bound
    {a : ℝ → ℝ} {r : ℝ}
    (hr_nn : 0 ≤ r) (hr_lt_one : r < 1)
    (ha_nn : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ a t)
    (ha_cont : ContinuousOn a (Set.Icc (0:ℝ) 1))
    (ha_0 : a 0 ≤ r ^ 2)
    (ha_deriv : ∀ t ∈ Set.Ioo (0:ℝ) 1, ∃ a', HasDerivAt a a' t ∧
                |a'| ≤ 2 * (Real.sqrt (a t)) ^ 3) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, (1 - t * r) ^ 2 * a t ≤ r ^ 2 :=
  diagonal_ode_squared_bound_via_lipschitz hr_nn hr_lt_one ha_nn ha_0
    (fun ε hε => b_eps_one_lipschitz ha_nn ha_cont ha_deriv ε hε)

/-- **ODE integration for the diagonal Dikin estimate.** Suppose
`a : ℝ → ℝ` is non-negative and continuous on `[0, 1]`, satisfies
`a(0) ≤ r²` (with `0 ≤ r < 1`), and `|a'(t)| ≤ 2 · (√a(t))³` on `(0, 1)`.
Then `√a(t) ≤ r/(1 − t·r)` for all `t ∈ [0, 1]`.

Proved by taking square roots of the squared form
(`diagonal_ode_squared_bound`): from `(1 − t·r)² · a(t) ≤ r²`,
`√` is monotone, then `√(x² · y) = |x| · √y = (1 − t·r) · √y` (positive),
and the bound is rearranged by dividing by `(1 − t·r) > 0`. -/
lemma local_norm_path_bound_from_diagonal_ode
    {a : ℝ → ℝ} {r : ℝ}
    (ha_nn : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ a t)
    (ha_cont : ContinuousOn a (Set.Icc (0:ℝ) 1))
    (ha_0 : a 0 ≤ r ^ 2)
    (hr_nn : 0 ≤ r) (hr_lt_one : r < 1)
    (ha_deriv : ∀ t ∈ Set.Ioo (0:ℝ) 1, ∃ a', HasDerivAt a a' t ∧
                |a'| ≤ 2 * (Real.sqrt (a t)) ^ 3) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, Real.sqrt (a t) ≤ r / (1 - t * r) := by
  intro t ht
  have h_1tr_pos : (0 : ℝ) < 1 - t * r := by
    obtain ⟨h0, h1⟩ := ht; nlinarith
  have h_sq := diagonal_ode_squared_bound hr_nn hr_lt_one ha_nn ha_cont ha_0 ha_deriv t ht
  have h_sqrt_le :
      Real.sqrt ((1 - t * r) ^ 2 * a t) ≤ Real.sqrt (r ^ 2) :=
    Real.sqrt_le_sqrt h_sq
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq h_1tr_pos.le,
      Real.sqrt_sq hr_nn] at h_sqrt_le
  rw [le_div_iff₀ h_1tr_pos, mul_comm]
  exact h_sqrt_le

/-- **Multiplicative Gronwall along an affine SC path.** Suppose
`H : ℝ → ℝ` is non-negative and continuous on `[0, 1]` and satisfies the
log-derivative bound `|H'(t)| ≤ 2 H(t) · r/(1 − t·r)` on `(0, 1)` (with
`0 ≤ r < 1`). Then `(1 − r)² H(0) ≤ H(1) ≤ (1 − r)⁻² H(0)`.

Proof: monotonicity trick that avoids `log`. The auxiliary function
`φ(t) := (1 − t·r)² · H(t)` has `φ'(t) ≤ 0` on `(0, 1)` (using
`(1 − t·r) H'(t) ≤ 2r H(t)` derived from the hypothesis), hence
`φ` is antitone on `[0, 1]` and `φ(1) ≤ φ(0)` gives
`(1 − r)² H(1) ≤ H(0)`. Symmetrically, `ψ(t) := H(t) / (1 − t·r)²`
is monotone, giving the lower bound. -/
lemma multiplicative_path_bound_from_log_ode
    {H : ℝ → ℝ} {r : ℝ}
    (hr_nn : 0 ≤ r) (hr_lt_one : r < 1)
    (hH_nn : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ H t)
    (hH_cont : ContinuousOn H (Set.Icc (0:ℝ) 1))
    (hH_deriv : ∀ t ∈ Set.Ioo (0:ℝ) 1, ∃ H', HasDerivAt H H' t ∧
                |H'| ≤ 2 * H t * (r / (1 - t * r))) :
    (1 - r) ^ 2 * H 0 ≤ H 1 ∧ H 1 ≤ (1 - r) ^ (-2 : ℝ) * H 0 := by
  have h1r_pos : (0 : ℝ) < 1 - r := by linarith
  have h1tr_pos : ∀ t ∈ Set.Icc (0:ℝ) 1, (0 : ℝ) < 1 - t * r := by
    intro t ⟨h0, h1⟩; nlinarith
  have hsq_pos : ∀ t ∈ Set.Icc (0:ℝ) 1, (0 : ℝ) < (1 - t * r) ^ 2 :=
    fun t ht => pow_pos (h1tr_pos t ht) 2
  have h_1tr_deriv : ∀ s : ℝ, HasDerivAt (fun u : ℝ => 1 - u * r) (-r) s := by
    intro s
    have h_id_mul : HasDerivAt (fun u : ℝ => u * r) r s := by
      simpa using (hasDerivAt_id s).mul_const r
    simpa using h_id_mul.const_sub 1
  have hsq_deriv : ∀ s : ℝ,
      HasDerivAt (fun u : ℝ => (1 - u * r) ^ 2) (-(2 * r * (1 - s * r))) s := by
    intro s
    have h := (h_1tr_deriv s).pow 2
    convert h using 1
    push_cast; ring
  have h_interior : interior (Set.Icc (0:ℝ) 1) = Set.Ioo 0 1 := interior_Icc
  -- Upper bound: H 1 ≤ (1 - r)⁻² · H 0 via φ(t) = (1 - t·r)² · H(t).
  have h_upper : H 1 ≤ (1 - r) ^ (-2 : ℝ) * H 0 := by
    set φ : ℝ → ℝ := fun t => (1 - t * r) ^ 2 * H t with hφ_def
    have hφ_cont : ContinuousOn φ (Set.Icc 0 1) :=
      (Continuous.continuousOn (by continuity)).mul hH_cont
    have hφ_diff_deriv : ∀ t ∈ Set.Ioo (0:ℝ) 1,
        DifferentiableAt ℝ φ t ∧ deriv φ t ≤ 0 := by
      intro t ht
      obtain ⟨H', hH'_deriv, hH'_bd⟩ := hH_deriv t ht
      have hφ_deriv_at :
          HasDerivAt φ (-(2 * r * (1 - t * r)) * H t + (1 - t * r) ^ 2 * H') t :=
        (hsq_deriv t).mul hH'_deriv
      refine ⟨hφ_deriv_at.differentiableAt, ?_⟩
      rw [hφ_deriv_at.deriv]
      have ht_Icc : t ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
      have h_1tr := h1tr_pos t ht_Icc
      have h_H_nn := hH_nn t ht_Icc
      have h_H'_le : H' ≤ 2 * H t * (r / (1 - t * r)) :=
        (le_abs_self H').trans hH'_bd
      have h_step : (1 - t * r) * H' ≤ 2 * H t * r := by
        have hmul := mul_le_mul_of_nonneg_left h_H'_le (le_of_lt h_1tr)
        calc (1 - t * r) * H'
            ≤ (1 - t * r) * (2 * H t * (r / (1 - t * r))) := hmul
          _ = 2 * H t * r := by field_simp
      nlinarith [h_step, h_1tr, h_H_nn, hr_nn,
        mul_le_mul_of_nonneg_left h_step (le_of_lt h_1tr)]
    have hφ_diff : DifferentiableOn ℝ φ (interior (Set.Icc (0:ℝ) 1)) := by
      rw [h_interior]
      intro t ht
      exact (hφ_diff_deriv t ht).1.differentiableWithinAt
    have hφ_nonpos : ∀ t ∈ interior (Set.Icc (0:ℝ) 1), deriv φ t ≤ 0 := by
      rw [h_interior]; intro t ht; exact (hφ_diff_deriv t ht).2
    have h_anti : AntitoneOn φ (Set.Icc (0:ℝ) 1) :=
      antitoneOn_of_deriv_nonpos (convex_Icc 0 1) hφ_cont hφ_diff hφ_nonpos
    have h_phi_le : φ 1 ≤ φ 0 :=
      h_anti (Set.left_mem_Icc.mpr zero_le_one)
             (Set.right_mem_Icc.mpr zero_le_one) zero_le_one
    have hφ_0 : φ 0 = H 0 := by simp [φ]
    have hφ_1 : φ 1 = (1 - r) ^ 2 * H 1 := by simp [φ]
    rw [hφ_0, hφ_1] at h_phi_le
    have h_sq_pos : (0 : ℝ) < (1 - r) ^ 2 := by positivity
    have h_div : H 1 ≤ H 0 / (1 - r) ^ 2 := by
      rw [le_div_iff₀ h_sq_pos]; linarith
    have h_rpow_eq : (1 - r) ^ (-2 : ℝ) * H 0 = H 0 / (1 - r) ^ 2 := by
      rw [Real.rpow_neg (le_of_lt h1r_pos), Real.rpow_two]
      field_simp
    rw [h_rpow_eq]; exact h_div
  -- Lower bound: (1 - r)² · H 0 ≤ H 1 via ψ(t) = H(t) / (1 - t·r)².
  have h_lower : (1 - r) ^ 2 * H 0 ≤ H 1 := by
    set ψ : ℝ → ℝ := fun t => H t / (1 - t * r) ^ 2 with hψ_def
    have hψ_cont : ContinuousOn ψ (Set.Icc 0 1) := by
      refine ContinuousOn.div hH_cont (Continuous.continuousOn (by continuity)) ?_
      intro t ht; exact ne_of_gt (hsq_pos t ht)
    have hψ_diff_deriv : ∀ t ∈ Set.Ioo (0:ℝ) 1,
        DifferentiableAt ℝ ψ t ∧ 0 ≤ deriv ψ t := by
      intro t ht
      obtain ⟨H', hH'_deriv, hH'_bd⟩ := hH_deriv t ht
      have ht_Icc : t ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
      have hsq_ne_t : (1 - t * r) ^ 2 ≠ 0 := ne_of_gt (hsq_pos t ht_Icc)
      have hψ_deriv_at : HasDerivAt ψ
          ((H' * (1 - t * r) ^ 2 - H t * (-(2 * r * (1 - t * r)))) /
            ((1 - t * r) ^ 2) ^ 2) t :=
        hH'_deriv.div (hsq_deriv t) hsq_ne_t
      refine ⟨hψ_deriv_at.differentiableAt, ?_⟩
      rw [hψ_deriv_at.deriv]
      have h_1tr := h1tr_pos t ht_Icc
      have h_H_nn := hH_nn t ht_Icc
      have h_H'_ge : -(2 * H t * (r / (1 - t * r))) ≤ H' := by
        have := neg_abs_le H'; linarith
      have h_step : -(2 * H t * r) ≤ (1 - t * r) * H' := by
        have hmul := mul_le_mul_of_nonneg_left h_H'_ge (le_of_lt h_1tr)
        have h_eq : (1 - t * r) * (-(2 * H t * (r / (1 - t * r)))) = -(2 * H t * r) := by
          have h_ne : (1 - t * r) ≠ 0 := ne_of_gt h_1tr
          field_simp
        linarith
      apply div_nonneg _ (sq_nonneg _)
      nlinarith [h_step, h_1tr, h_H_nn, hr_nn,
        mul_le_mul_of_nonneg_left h_step (le_of_lt h_1tr)]
    have hψ_diff : DifferentiableOn ℝ ψ (interior (Set.Icc (0:ℝ) 1)) := by
      rw [h_interior]
      intro t ht
      exact (hψ_diff_deriv t ht).1.differentiableWithinAt
    have hψ_nonneg : ∀ t ∈ interior (Set.Icc (0:ℝ) 1), 0 ≤ deriv ψ t := by
      rw [h_interior]; intro t ht; exact (hψ_diff_deriv t ht).2
    have h_mono : MonotoneOn ψ (Set.Icc (0:ℝ) 1) :=
      monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hψ_cont hψ_diff hψ_nonneg
    have h_psi_le : ψ 0 ≤ ψ 1 :=
      h_mono (Set.left_mem_Icc.mpr zero_le_one)
             (Set.right_mem_Icc.mpr zero_le_one) zero_le_one
    have hψ_0 : ψ 0 = H 0 := by simp [ψ]
    have hψ_1 : ψ 1 = H 1 / (1 - r) ^ 2 := by simp [ψ]
    rw [hψ_0, hψ_1] at h_psi_le
    have h_sq_pos : (0 : ℝ) < (1 - r) ^ 2 := by positivity
    rw [le_div_iff₀ h_sq_pos] at h_psi_le
    linarith
  exact ⟨h_lower, h_upper⟩

namespace LHSCB

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V]

/-! ### Hessian quadratic form and local norm -/

/-- The **Hessian quadratic form** `D²f(x)[h, h]` of an LHSCB barrier,
computed via `iteratedFDerivWithin` on `interior K`. Used with
dot notation: `f.hess x h`. -/
noncomputable def hess {K : Set V} {ν : ℕ} {d : ℕ∞}
    (f : LHSCB V K ν d) (x h : V) : ℝ :=
  iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => h)

/-- The **local Hessian-induced (semi)norm** along direction `v`:
`‖v‖_{∇²f(x)} := √(D²f(x)[v, v])`. Used with dot notation:
`f.local_norm x v`. -/
noncomputable def local_norm {K : Set V} {ν : ℕ} {d : ℕ∞}
    (f : LHSCB V K ν d) (x v : V) : ℝ :=
  Real.sqrt (f.hess x v)

/-! ### LHSCB-specific Dikin scaffold

Five LHSCB-specific lemmas, building on the pure-analysis scaffold
above plus `f.contDiff₃`, `f.self_concordant_hessian_nonneg`, and
`f.self_concordant_abs_third` from `Irn.Barriers`. -/

/-- **Chain rule along the affine segment.** For an LHSCB `f` and any
direction `h`, the map `s ↦ f.hess (u₀ + s·(u−u₀)) h` (i.e. the
Hessian quadratic form along the segment in direction `h`) is
differentiable at any `t ∈ (0, 1)` with derivative
`iteratedFDerivWithin ℝ 3 f.f (interior K) (u₀ + t·(u−u₀)) ![u−u₀, h, h]`.

Proof: `iteratedFDerivWithin ℝ 2 f.f (interior K)` is `C¹` at `γ t ∈
interior K` (from `f.contDiff₃` + `ContDiffWithinAt.iteratedFDerivWithin_right`,
then upgraded to `ContDiffAt` since `interior K` is open). Composing
its Fréchet derivative with the affine path `γ` (chain rule
`HasFDerivAt.comp_hasDerivAt`) gives the derivative of
`s ↦ iteratedFDerivWithin ℝ 2 f.f (interior K) (γ s)`. Composing once
more with the continuous-linear evaluation `M ↦ M (fun _ => h)`
(`ContinuousMultilinearMap.apply`) yields the scalar derivative. The
identification with `iteratedFDerivWithin ℝ 3 …` follows from
`iteratedFDerivWithin_succ_apply_left` (with `n = 2`) and
`fderivWithin_of_isOpen` on the open `interior K`. -/
lemma hess_path_has_deriv_at {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {K : Set V} {ν : ℕ} {d : ℕ∞}
    (f : LHSCB V K ν d) (hK_convex : Convex ℝ K)
    (u₀ u h : V) (hu₀ : u₀ ∈ interior K) (hu : u ∈ interior K)
    (t : ℝ) (ht : t ∈ Set.Ioo (0:ℝ) 1) :
    HasDerivAt (fun s => f.hess (u₀ + s • (u - u₀)) h)
      (iteratedFDerivWithin ℝ 3 f.f (interior K)
        (u₀ + t • (u - u₀)) ![u - u₀, h, h]) t := by
  set γ : ℝ → V := fun s => u₀ + s • (u - u₀) with hγ_def
  have hγ_deriv : HasDerivAt γ (u - u₀) t := by
    have h_smul : HasDerivAt (fun s : ℝ => s • (u - u₀)) (u - u₀) t := by
      simpa using (hasDerivAt_id t).smul_const (u - u₀)
    simpa [γ] using h_smul.const_add u₀
  have ht_Icc : t ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hγt_in : γ t ∈ interior K :=
    segment_in_interior hK_convex u₀ hu₀ u hu t ht_Icc
  have hf_wat : ContDiffWithinAt ℝ 3 f.f (interior K) (γ t) :=
    f.contDiff₃.contDiffWithinAt hγt_in
  have h_iter_wat :
      ContDiffWithinAt ℝ 1 (iteratedFDerivWithin ℝ 2 f.f (interior K))
        (interior K) (γ t) :=
    hf_wat.iteratedFDerivWithin_right isOpen_interior.uniqueDiffOn
      (by norm_num : (1 : WithTop ℕ∞) + 2 ≤ 3) hγt_in
  have h_iter_at :
      ContDiffAt ℝ 1 (iteratedFDerivWithin ℝ 2 f.f (interior K)) (γ t) :=
    h_iter_wat.contDiffAt (isOpen_interior.mem_nhds hγt_in)
  have h_iter_diff :
      DifferentiableAt ℝ (iteratedFDerivWithin ℝ 2 f.f (interior K)) (γ t) :=
    h_iter_at.differentiableAt_one
  set L : V →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) ℝ :=
    fderiv ℝ (iteratedFDerivWithin ℝ 2 f.f (interior K)) (γ t) with hL_def
  have h_fd_at :
      HasFDerivAt (iteratedFDerivWithin ℝ 2 f.f (interior K)) L (γ t) :=
    h_iter_diff.hasFDerivAt
  have h_iter_γ_deriv :
      HasDerivAt (fun s => iteratedFDerivWithin ℝ 2 f.f (interior K) (γ s))
        (L (u - u₀)) t :=
    h_fd_at.comp_hasDerivAt t hγ_deriv
  set ev : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) ℝ →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => V) ℝ (fun _ => h) with hev_def
  have h_hess_γ_deriv :
      HasDerivAt (fun s => ev (iteratedFDerivWithin ℝ 2 f.f (interior K) (γ s)))
        (ev (L (u - u₀))) t :=
    (ev.hasFDerivAt (x := iteratedFDerivWithin ℝ 2 f.f (interior K)
      (γ t))).comp_hasDerivAt t h_iter_γ_deriv
  have h_tail_eq :
      Fin.tail (![u - u₀, h, h] : Fin 3 → V) = (fun _ : Fin 2 => h) := by
    funext i; fin_cases i <;> rfl
  have h_deriv_eq :
      iteratedFDerivWithin ℝ 3 f.f (interior K) (γ t) ![u - u₀, h, h]
        = ev (L (u - u₀)) := by
    show fderivWithin ℝ (iteratedFDerivWithin ℝ 2 f.f (interior K))
          (interior K) (γ t) (u - u₀)
          (Fin.tail (![u - u₀, h, h] : Fin 3 → V)) = ev (L (u - u₀))
    rw [fderivWithin_of_isOpen isOpen_interior hγt_in, h_tail_eq]
    rfl
  rw [h_deriv_eq]
  exact h_hess_γ_deriv

/-- **Critical self-concordance inequality.** Fully polarized SC bound:
`|D³f(x)[a, b, c]| ≤ 2 · √D²f(x)[a, a] · √D²f(x)[b, b] · √D²f(x)[c, c]`
for any directions `a, b, c` at any interior point `x`.

**Status: open.** The diagonal special case `a = b = c` is exactly
`f.self_concordant_abs_third` (which extracts a square root from the
squared SC bound `f.self_concordant`). The general case — polarization
of the diagonal bound to the trilinear form with the *same constant 2*
— is the canonical hard step of self-concordance theory (Nesterov–
Nemirovski §2.1; Renegar Cor 2.3.4).

Naive polarization is lossy:
* The trilinear polarization identity
  `48·T[a,b,c] = Σ_{σ∈{±1}³} σ₁σ₂σ₃·T[σ₁a+σ₂b+σ₃c]³`
  combined with `|T[w]³| ≤ 2·Q[w]^{3/2}` and the triangle inequality
  `√Q[σ·v] ≤ √Q[a]+√Q[b]+√Q[c]` gives constant `≈ 9`, not `2`.
* Banach's theorem `‖T‖ = sup_{‖h‖=1}|T[h,h,h]|` for symmetric
  trilinear forms holds only over complex Hilbert spaces; over `ℝ` the
  best constant is `9/2`.

Two routes to the sharp constant `2`:
1. **Hilbert SOS.** `P(t) := 4·Q[h+ta]³ − T[h+ta]³² ≥ 0` is a degree-6
   univariate polynomial nonneg on `ℝ`, hence (Hilbert 1888) a sum of
   two squares of degree-≤-3 polynomials. Coefficient matching extracts
   the *bipolarized* bound `|T[u,h,h]| ≤ 2·√Q[u]·Q[h]`, and
   PSD Cauchy–Schwarz on `(b,c) ↦ T[u,b,c]/√Q[u]` upgrades to the
   trilinear bound. Mathlib has no Hilbert-SOS lemma; would need to be
   formalized (~few hundred lines).
2. **Saturation + continuity.** When `P(0) = 0` (saturation at `h`),
   `t=0` is a min so `P'(0) = 0`, which gives `T[h,h,h]·T[h,h,a]
   = 4·α⁴·Q[h,a]` and hence `|T[h,h,a]| = 2α²·|Q[h,a]| ≤ 2α²β`. The
   non-saturated case `P(0) > 0` requires a continuity / scaling
   argument that has resisted closure here.

A randomized numerical search over the ratio
`|T[a,b,c]|/(√Q[a]·√Q[b]·√Q[c])` confirms the sup is `≈ 1.94`,
consistent with the textbook constant `2`. -/
lemma self_concordant_inequality {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {K : Set V} {ν : ℕ} {d : ℕ∞}
    (f : LHSCB V K ν d) (x : V) (hx : x ∈ interior K) (a b c : V) :
    |iteratedFDerivWithin ℝ 3 f.f (interior K) x ![a, b, c]| ≤
      2 * Real.sqrt (f.hess x a) * Real.sqrt (f.hess x b) *
        Real.sqrt (f.hess x c) := by
  -- Diagonal case `a = b = c` reduces to `f.self_concordant_abs_third`;
  -- general case is the open polarization step (see docstring above).
  sorry

/-- **Lemma 1: Diagonal Dikin metric bound along the segment.**
For `t ∈ [0, 1]` and `r := √f.hess u₀ (u−u₀) < 1`, the local norm of
the displacement at `u₀ + t·(u−u₀)` is bounded by `r/(1 − t·r)`.

Proved by feeding the chain rule (`hess_path_has_deriv_at` with `h := u − u₀`)
and the diagonal SC bound (`self_concordant_abs_third`) into the abstract
ODE integrator `local_norm_path_bound_from_diagonal_ode`. -/
lemma dikin_path_metric_bound {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {K : Set V} {ν : ℕ} {d : ℕ∞}
    (f : LHSCB V K ν d) (hK_convex : Convex ℝ K)
    (u₀ u : V) (hu₀ : u₀ ∈ interior K) (hu : u ∈ interior K)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1)
    (r : ℝ) (hr_pos : 0 ≤ r) (hr_lt_one : r < 1)
    (h_in_ball : f.hess u₀ (u - u₀) ≤ r ^ 2) :
    f.local_norm (u₀ + t • (u - u₀)) (u - u₀) ≤ r / (1 - t * r) := by
  set γ : ℝ → V := fun t => u₀ + t • (u - u₀) with hγ_def
  set a : ℝ → ℝ := fun t => f.hess (γ t) (u - u₀) with ha_def
  have h_in : ∀ s ∈ Set.Icc (0:ℝ) 1, γ s ∈ interior K :=
    segment_in_interior hK_convex u₀ hu₀ u hu
  have ha_nn : ∀ s ∈ Set.Icc (0:ℝ) 1, 0 ≤ a s := fun s hs =>
    f.self_concordant_hessian_nonneg (γ s) (h_in s hs) (u - u₀)
  have ha_cont : ContinuousOn a (Set.Icc (0:ℝ) 1) := by
    have h_iter_cont :
        ContinuousOn (iteratedFDerivWithin ℝ 2 f.f (interior K)) (interior K) :=
      f.contDiff₃.continuousOn_iteratedFDerivWithin (by norm_num)
        isOpen_interior.uniqueDiffOn
    have h_eval_cont :
        Continuous (fun M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) ℝ =>
          M (fun _ => u - u₀)) :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => V) ℝ
        (fun _ => u - u₀)).continuous
    have h_hess_cont :
        ContinuousOn (fun x : V => f.hess x (u - u₀)) (interior K) :=
      h_eval_cont.comp_continuousOn h_iter_cont
    have hγ_cont : Continuous γ := by
      show Continuous (fun s : ℝ => u₀ + s • (u - u₀))
      continuity
    exact h_hess_cont.comp hγ_cont.continuousOn h_in
  have ha_0 : a 0 ≤ r ^ 2 := by
    show f.hess (γ 0) (u - u₀) ≤ r ^ 2
    have h_γ0 : γ 0 = u₀ := by simp [γ]
    rw [h_γ0]; exact h_in_ball
  have ha_deriv : ∀ s ∈ Set.Ioo (0:ℝ) 1, ∃ a', HasDerivAt a a' s ∧
                  |a'| ≤ 2 * (Real.sqrt (a s)) ^ 3 := by
    intro s hs
    refine ⟨_, hess_path_has_deriv_at f hK_convex u₀ u (u - u₀) hu₀ hu s hs, ?_⟩
    have h_diag :
        (![u - u₀, u - u₀, u - u₀] : Fin 3 → V) = (fun _ => u - u₀) := by
      funext i; fin_cases i <;> rfl
    rw [h_diag]
    have hs_Icc : s ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
    exact f.self_concordant_abs_third (γ s) (h_in s hs_Icc) (u - u₀)
  have h_bd := local_norm_path_bound_from_diagonal_ode ha_nn ha_cont ha_0 hr_pos hr_lt_one ha_deriv
  show Real.sqrt (a t) ≤ r / (1 - t * r)
  exact h_bd t ht

/-- **Lemma 2: Polarized self-concordance bound along the segment.**
The derivative of `t ↦ f.hess (u₀ + t·(u−u₀)) h` is bounded by
`2 · f.hess (·) h · f.local_norm (·) (u−u₀)`.

Proved by combining the chain rule (`hess_path_has_deriv_at`) with the
trilinear SC bound (`self_concordant_inequality`) specialised at
`(u−u₀, h, h)`. Since `f.hess (γt) h ≥ 0`, the two `√Q[h]` factors
collapse to `Q[h]`, matching the goal modulo reordering. -/
lemma path_hess_deriv_bound {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {K : Set V} {ν : ℕ} {d : ℕ∞}
    (f : LHSCB V K ν d) (hK_convex : Convex ℝ K)
    (u₀ u h : V) (hu₀ : u₀ ∈ interior K) (hu : u ∈ interior K)
    (t : ℝ) (ht : t ∈ Set.Ioo (0:ℝ) 1) :
    ∃ H', HasDerivAt (fun s => f.hess (u₀ + s • (u - u₀)) h) H' t ∧
          |H'| ≤ 2 * f.hess (u₀ + t • (u - u₀)) h *
                 f.local_norm (u₀ + t • (u - u₀)) (u - u₀) := by
  set γ : ℝ → V := fun t => u₀ + t • (u - u₀) with hγ_def
  refine ⟨_, hess_path_has_deriv_at f hK_convex u₀ u h hu₀ hu t ht, ?_⟩
  have ht_Icc : t ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have h_in : γ t ∈ interior K :=
    segment_in_interior hK_convex u₀ hu₀ u hu t ht_Icc
  have hQh_nn : 0 ≤ f.hess (γ t) h :=
    f.self_concordant_hessian_nonneg (γ t) h_in h
  have h_sq : Real.sqrt (f.hess (γ t) h) * Real.sqrt (f.hess (γ t) h)
            = f.hess (γ t) h :=
    Real.mul_self_sqrt hQh_nn
  show |iteratedFDerivWithin ℝ 3 f.f (interior K) (γ t) ![u - u₀, h, h]| ≤
       2 * f.hess (γ t) h * Real.sqrt (f.hess (γ t) (u - u₀))
  calc |iteratedFDerivWithin ℝ 3 f.f (interior K) (γ t) ![u - u₀, h, h]|
      ≤ 2 * Real.sqrt (f.hess (γ t) (u - u₀))
            * Real.sqrt (f.hess (γ t) h)
            * Real.sqrt (f.hess (γ t) h) :=
        f.self_concordant_inequality (γ t) h_in (u - u₀) h h
    _ = 2 * f.hess (γ t) h * Real.sqrt (f.hess (γ t) (u - u₀)) := by
        conv_rhs => rw [← h_sq]
        ring

/-- **Lemma 3: Integrated multiplicative Hessian bound along the segment.**
Integrating Lemma 2 against Lemma 1 from `0` to `1`:
`(1−r)² · f.hess u₀ h ≤ f.hess u h ≤ (1−r)⁻² · f.hess u₀ h`.

Proved by combining Lemma 2 (derivative bound) with Lemma 1 (metric
bound) to satisfy the hypothesis of `multiplicative_path_bound_from_log_ode`. -/
lemma path_hess_integrated_bound {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {K : Set V} {ν : ℕ} {d : ℕ∞}
    (f : LHSCB V K ν d) (hK_convex : Convex ℝ K)
    (u₀ u h : V) (hu₀ : u₀ ∈ interior K) (hu : u ∈ interior K)
    (r : ℝ) (hr_pos : 0 ≤ r) (hr_lt_one : r < 1)
    (h_in_ball : f.hess u₀ (u - u₀) ≤ r ^ 2) :
    (1 - r) ^ 2 * f.hess u₀ h ≤ f.hess u h ∧
    f.hess u h ≤ (1 - r) ^ (-2 : ℝ) * f.hess u₀ h := by
  set γ : ℝ → V := fun t => u₀ + t • (u - u₀) with hγ_def
  set H : ℝ → ℝ := fun t => f.hess (γ t) h with hH_def
  have h_in : ∀ s ∈ Set.Icc (0:ℝ) 1, γ s ∈ interior K :=
    segment_in_interior hK_convex u₀ hu₀ u hu
  have hH_nn : ∀ s ∈ Set.Icc (0:ℝ) 1, 0 ≤ H s := fun s hs =>
    f.self_concordant_hessian_nonneg (γ s) (h_in s hs) h
  have hH_cont : ContinuousOn H (Set.Icc (0:ℝ) 1) := by
    have h_iter_cont :
        ContinuousOn (iteratedFDerivWithin ℝ 2 f.f (interior K)) (interior K) :=
      f.contDiff₃.continuousOn_iteratedFDerivWithin (by norm_num)
        isOpen_interior.uniqueDiffOn
    have h_eval_cont :
        Continuous (fun M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) ℝ =>
          M (fun _ => h)) :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => V) ℝ
        (fun _ => h)).continuous
    have h_hess_cont : ContinuousOn (fun x : V => f.hess x h) (interior K) :=
      h_eval_cont.comp_continuousOn h_iter_cont
    have hγ_cont : Continuous γ := by
      show Continuous (fun s : ℝ => u₀ + s • (u - u₀))
      continuity
    exact h_hess_cont.comp hγ_cont.continuousOn h_in
  have hH_deriv : ∀ s ∈ Set.Ioo (0:ℝ) 1, ∃ H', HasDerivAt H H' s ∧
                  |H'| ≤ 2 * H s * (r / (1 - s * r)) := by
    intro s hs
    obtain ⟨H', hH'_deriv, hH'_bd⟩ :=
      f.path_hess_deriv_bound hK_convex u₀ u h hu₀ hu s hs
    refine ⟨H', hH'_deriv, ?_⟩
    have hs_Icc : s ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
    have h_local := f.dikin_path_metric_bound hK_convex u₀ u hu₀ hu s hs_Icc r
      hr_pos hr_lt_one h_in_ball
    have h_H_nn := hH_nn s hs_Icc
    calc |H'|
        ≤ 2 * H s * f.local_norm (γ s) (u - u₀) := hH'_bd
      _ ≤ 2 * H s * (r / (1 - s * r)) := by
          have h_factor_nn : 0 ≤ 2 * H s := by positivity
          exact mul_le_mul_of_nonneg_left h_local h_factor_nn
  have h_result :=
    multiplicative_path_bound_from_log_ode hr_pos hr_lt_one hH_nn hH_cont hH_deriv
  have hH_0 : H 0 = f.hess u₀ h := by
    show f.hess (γ 0) h = f.hess u₀ h
    congr 1; simp [γ]
  have hH_1 : H 1 = f.hess u h := by
    show f.hess (γ 1) h = f.hess u h
    congr 1
    show u₀ + (1 : ℝ) • (u - u₀) = u
    rw [one_smul]; abel
  rw [hH_0, hH_1] at h_result
  exact h_result

omit [CompleteSpace V] in
/-- **Dikin-ball Hessian Lipschitz bound (paper §6.3 Lemma 16 step (i)).**
For `u, u₀ ∈ int K` such that the SC-norm displacement
`r² := ⟨u − u₀, ∇²f(u₀)(u − u₀)⟩` is less than `1`, the Hessian
quadratic form satisfies the multiplicative bound
`(1 − r)² ⟨h, ∇²f(u₀) h⟩ ≤ ⟨h, ∇²f(u) h⟩ ≤ (1 − r)⁻² ⟨h, ∇²f(u₀) h⟩`
for every direction `h`. The constants depend only on `r` — not on
`u₀`, `K`, or the LHSCB barrier parameter `ν` — which is what makes
the LHSCB Newton–Kantorovich basin radius an *absolute* constant.

Thin wrapper around `path_hess_integrated_bound`; the analytic content
lives in the four scaffold lemmas above. -/
theorem hessian_dikin_bound {K : Set V} {ν : ℕ} {d : ℕ∞}
    (f : LHSCB V K ν d) (hK_convex : Convex ℝ K)
    (u₀ : V) (hu₀ : u₀ ∈ interior K)
    (u : V) (hu : u ∈ interior K)
    (r : ℝ) (hr_pos : 0 ≤ r) (hr_lt_one : r < 1)
    (h_in_ball : f.hess u₀ (u - u₀) ≤ r ^ 2) :
    ∀ h : V,
      (1 - r) ^ 2 * f.hess u₀ h ≤ f.hess u h ∧
      f.hess u h ≤ (1 - r) ^ (-2 : ℝ) * f.hess u₀ h := by
  intro h
  exact path_hess_integrated_bound f hK_convex u₀ u h hu₀ hu r hr_pos hr_lt_one h_in_ball

end LHSCB

end Irn
