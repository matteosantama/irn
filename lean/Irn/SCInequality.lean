/-
# Self-concordance polarization inequality

Helper lemmas for the proof of `LHSCB.self_concordant_inequality`.
-/

import Mathlib
import Irn.Barriers

namespace Irn

set_option maxHeartbeats 400000

open LHSCB

/-! ### Multilinearity helpers for ContinuousMultilinearMap with matrix notation -/

section MultilinearHelpers

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-
Additivity in the first argument of a `ContinuousMultilinearMap` on `Fin 3`.
-/
lemma cmmap_add_first (M : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => V) ℝ)
    (a₁ a₂ b c : V) :
    M ![a₁ + a₂, b, c] = M ![a₁, b, c] + M ![a₂, b, c] := by
  -- By definition of the continuous multilinear map, we can rewrite the goal using the fact that it is multilinear.
  have h_multilinear : ∀ (a₁ a₂ b c : V), M ![a₁ + a₂, b, c] = M ![a₁, b, c] + M ![a₂, b, c] := by
    intro a₁ a₂ b c
    have h_multilinear : M (Function.update ![a₁, b, c] 0 (a₁ + a₂)) = M (Function.update ![a₁, b, c] 0 a₁) + M (Function.update ![a₁, b, c] 0 a₂) := by
      convert M.map_update_add _ _ _ _ using 1;
    convert h_multilinear using 1 <;> congr <;> ext i <;> fin_cases i <;> rfl;
  exact h_multilinear a₁ a₂ b c

/-
Scalar multiplication in the first argument.
-/
lemma cmmap_smul_first (M : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => V) ℝ)
    (t : ℝ) (a b c : V) :
    M ![t • a, b, c] = t * M ![a, b, c] := by
  convert M.map_smul_univ _ _ using 2;
  rotate_right;
  exacts [ fun i => if i = 0 then t else 1, by ext i; fin_cases i <;> simp +decide, by simp +decide [ Fin.prod_univ_three ] ]

/-
Additivity in the second argument.
-/
lemma cmmap_add_second (M : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => V) ℝ)
    (a b₁ b₂ c : V) :
    M ![a, b₁ + b₂, c] = M ![a, b₁, c] + M ![a, b₂, c] := by
  convert M.map_update_add ![a, b₁, c] 1 b₁ b₂ using 1;
  · congr ; ext i ; fin_cases i <;> rfl;
  · congr! 2;
    · ext i; fin_cases i <;> rfl;
    · ext i; fin_cases i <;> rfl;

/-
Scalar multiplication in the second argument.
-/
lemma cmmap_smul_second (M : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => V) ℝ)
    (t : ℝ) (a b c : V) :
    M ![a, t • b, c] = t * M ![a, b, c] := by
  convert M.map_smul_univ ( fun i ↦ if i = 1 then t else 1 ) _ using 1;
  rotate_right;
  exact fun i => if i = 1 then b else if i = 0 then a else c;
  · exact congr_arg _ ( by ext i; fin_cases i <;> simp +decide );
  · simp +decide [ Fin.prod_univ_three, mul_comm ];
    exact Or.inl ( congr_arg M ( by ext i; fin_cases i <;> rfl ) )

/-- `![h, h, h]` equals `fun _ => h` as functions `Fin 3 → V`. -/
lemma vec3_const_eq (h : V) : (![h, h, h] : Fin 3 → V) = fun _ => h := by
  ext i; fin_cases i <;> rfl

/-- `![h, h]` equals `fun _ => h` as functions `Fin 2 → V`. -/
lemma vec2_const_eq (h : V) : (![h, h] : Fin 2 → V) = fun _ => h := by
  ext i; fin_cases i <;> rfl

/-
Additivity in the first argument of a `ContinuousMultilinearMap` on `Fin 2`.
-/
lemma cmmap2_add_first (M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) ℝ)
    (a₁ a₂ b : V) :
    M ![a₁ + a₂, b] = M ![a₁, b] + M ![a₂, b] := by
  convert M.map_update_add ![a₁, b] 0 a₁ a₂ using 1;
  · exact congr_arg _ ( by ext i; fin_cases i <;> rfl );
  · congr <;> ext i <;> fin_cases i <;> rfl

/-
Scalar multiplication in the first argument of `Fin 2`.
-/
lemma cmmap2_smul_first (M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) ℝ)
    (t : ℝ) (a b : V) :
    M ![t • a, b] = t * M ![a, b] := by
  convert M.map_smul_univ ( fun i => if i = 0 then t else 1 ) ( ![a, b] ) using 1;
  · exact congr_arg _ ( by ext i; fin_cases i <;> simp +decide );
  · simp +decide [ Fin.prod_univ_succ ]

/-
Additivity in the second argument of `Fin 2`.
-/
lemma cmmap2_add_second (M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) ℝ)
    (a b₁ b₂ : V) :
    M ![a, b₁ + b₂] = M ![a, b₁] + M ![a, b₂] := by
  convert M.map_update_add ( fun i => if i = 0 then a else if i = 1 then b₁ else b₂ ) 1 b₁ b₂ using 11;
  · exact funext fun i => by fin_cases i <;> simp +decide ;
  · ext i; fin_cases i <;> rfl;
  · exact funext fun i => by fin_cases i <;> simp +decide ;

/-
Scalar multiplication in the second argument of `Fin 2`.
-/
lemma cmmap2_smul_second (M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) ℝ)
    (t : ℝ) (a b : V) :
    M ![a, t • b] = t * M ![a, b] := by
  convert M.map_smul_univ ( fun i => if i = 1 then t else 1 ) ![a, b] using 1;
  · exact congr_arg _ ( by ext i; fin_cases i <;> simp +decide );
  · simp +decide [ Fin.prod_univ_two ]

/-
Subtraction in the first argument of `Fin 2`.
-/
lemma cmmap2_sub_first (M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) ℝ)
    (a₁ a₂ b : V) :
    M ![a₁ - a₂, b] = M ![a₁, b] - M ![a₂, b] := by
  -- By definition of subtraction, we can write $a₁ - a₂$ as $a₁ + (-a₂)$.
  have h_sub : M ![a₁ - a₂, b] = M ![a₁, b] + M ![-a₂, b] := by
    convert cmmap2_add_first M a₁ ( -a₂ ) b using 1 ; simp +decide [ sub_eq_add_neg ];
  have h_neg : M ![-a₂, b] = -M ![a₂, b] := by
    convert cmmap2_smul_first M ( -1 ) a₂ b using 1 <;> norm_num
  rw [h_sub, h_neg]
  ring

/-
Subtraction in the second argument of `Fin 2`.
-/
lemma cmmap2_sub_second (M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) ℝ)
    (a b₁ b₂ : V) :
    M ![a, b₁ - b₂] = M ![a, b₁] - M ![a, b₂] := by
  have h_sub : M ![a, b₁ - b₂] = M ![a, b₁] + M ![a, -b₂] := by
    convert cmmap2_add_second M a b₁ ( -b₂ ) using 1;
    rw [ sub_eq_add_neg ];
  have := cmmap2_smul_second M ( -1 ) a b₂; simp_all +decide [ sub_eq_add_neg ] ;

end MultilinearHelpers

/-! ### Symmetry of the third derivative -/

section ThirdDerivSymmetry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {K : Set V} {ν : ℕ} {d : ℕ∞}

/-
Symmetry of the Hessian: `D²f(x)[a, b] = D²f(x)[b, a]`.
-/
lemma hessian_symm (f : LHSCB V K ν d) (x : V) (hx : x ∈ interior K) (a b : V) :
    iteratedFDerivWithin ℝ 2 f.f (interior K) x ![a, b] =
    iteratedFDerivWithin ℝ 2 f.f (interior K) x ![b, a] := by
  have h_symm : IsSymmSndFDerivWithinAt ℝ f.f (interior K) x := by
    have h_diff : ContDiffOn ℝ 2 f.f (interior K) := by
      exact f.contDiff₃.of_le ( by norm_num );
    apply_rules [ ContDiffWithinAt.isSymmSndFDerivWithinAt ];
    exact h_diff.contDiffWithinAt hx;
    · norm_num [ minSmoothness ];
    · exact isOpen_interior.uniqueDiffOn;
    · exact subset_closure ( by simpa using hx );
  convert h_symm b a using 1;
  · rw [ iteratedFDerivWithin_succ_apply_right ];
    · rw [ iteratedFDerivWithin_one_apply ];
      · convert h_symm a b using 1;
      · exact isOpen_interior.uniqueDiffWithinAt hx;
    · exact isOpen_interior.uniqueDiffOn;
    · exact hx;
  · rw [ iteratedFDerivWithin_succ_apply_right ];
    · rw [ iteratedFDerivWithin_one_apply ];
      · convert h_symm b a using 1;
      · exact uniqueDiffWithinAt_of_mem_nhds ( IsOpen.mem_nhds isOpen_interior hx );
    · exact isOpen_interior.uniqueDiffOn;
    · exact hx

/-- Evaluation at a fixed vector is a CLM on `ContinuousMultilinearMap`. -/
noncomputable def evalCLM2 (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m : Fin 2 → V) : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) ℝ →L[ℝ] ℝ :=
  ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => V) ℝ m

/-- The composition of `iteratedFDerivWithin 2 f s` with evaluation at `m` equals
the function `y ↦ (iteratedFDerivWithin 2 f s y) m`. -/
lemma eval_comp_iteratedFDeriv2 {f : V → ℝ} {s : Set V} (m : Fin 2 → V) :
    (fun y => (iteratedFDerivWithin ℝ 2 f s y) m) =
    (evalCLM2 V m) ∘ (iteratedFDerivWithin ℝ 2 f s) := by
  ext y; rfl

/-
The fderivWithin of `y ↦ (D²f(y)) m` equals `(fderivWithin D²f s x a) m`,
under appropriate differentiability conditions.
-/
lemma fderivWithin_eval_iteratedFDeriv2 {f : V → ℝ} {s : Set V} {x : V}
    (hf : DifferentiableWithinAt ℝ (iteratedFDerivWithin ℝ 2 f s) s x)
    (hs : UniqueDiffWithinAt ℝ s x) (m : Fin 2 → V) :
    fderivWithin ℝ (fun y => (iteratedFDerivWithin ℝ 2 f s y) m) s x =
    (evalCLM2 V m).comp (fderivWithin ℝ (iteratedFDerivWithin ℝ 2 f s) s x) := by
  rw [ show ( fun y => ( iteratedFDerivWithin ℝ 2 f s y ) m ) = ( evalCLM2 V m ) ∘ ( iteratedFDerivWithin ℝ 2 f s ) from funext fun x => rfl, fderivWithin_comp ];
  any_goals assumption;
  rw [ ContinuousLinearMap.fderivWithin ];
  exact Set.univ;
  · exact uniqueDiffWithinAt_univ;
  · exact DifferentiableAt.differentiableWithinAt ( by exact ( evalCLM2 V m |> ContinuousLinearMap.differentiableAt ) );
  · exact Set.mapsTo_univ _ _

/-
The `iteratedFDerivWithin ℝ 2 f.f s` is differentiable within `s` at `x`
when `f` is `C³` on `s` and `s` has unique differentials.
-/
lemma iteratedFDerivWithin2_differentiableWithinAt
    {f : V → ℝ} {s : Set V}
    (hf : ContDiffOn ℝ 3 f s) (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) :
    DifferentiableWithinAt ℝ (iteratedFDerivWithin ℝ 2 f s) s x := by
  apply_rules [ ContDiffOn.differentiableOn_iteratedFDerivWithin ];
  exacts [ hf, by norm_cast ]

/-
The third derivative is symmetric in the last two arguments.
-/
lemma third_deriv_symm_23 (f : LHSCB V K ν d) (x : V) (hx : x ∈ interior K) (a b c : V) :
    iteratedFDerivWithin ℝ 3 f.f (interior K) x ![a, b, c] =
    iteratedFDerivWithin ℝ 3 f.f (interior K) x ![a, c, b] := by
  -- By definition of iteratedFDerivWithin, we have:
  have h_def : (iteratedFDerivWithin ℝ 3 f.f (interior K) x) ![a, b, c] = (fderivWithin ℝ (iteratedFDerivWithin ℝ 2 f.f (interior K)) (interior K) x a) ![b, c] := by
    rw [ iteratedFDerivWithin_succ_apply_left ] ; aesop;
  have h_def' : (iteratedFDerivWithin ℝ 3 f.f (interior K) x) ![a, c, b] = (fderivWithin ℝ (iteratedFDerivWithin ℝ 2 f.f (interior K)) (interior K) x a) ![c, b] := by
    rfl;
  rw [ h_def, h_def' ];
  -- By the definition of the derivative, we can write
  have h_deriv : (fderivWithin ℝ (iteratedFDerivWithin ℝ 2 f.f (interior K)) (interior K) x a) ![b, c] =
    (fderivWithin ℝ (fun y => (iteratedFDerivWithin ℝ 2 f.f (interior K) y) ![b, c]) (interior K) x) a := by
      rw [ fderivWithin_eval_iteratedFDeriv2 ];
      · rfl;
      · apply_rules [ iteratedFDerivWithin2_differentiableWithinAt ];
        · exact f.contDiff₃;
        · exact isOpen_interior.uniqueDiffOn;
      · exact uniqueDiffWithinAt_of_mem_nhds ( IsOpen.mem_nhds isOpen_interior hx );
  rw [ h_deriv, fderivWithin_congr ];
  rw [ fderivWithin_eval_iteratedFDeriv2 ];
  any_goals tauto;
  · apply_rules [ iteratedFDerivWithin2_differentiableWithinAt ];
    · exact f.contDiff₃;
    · exact isOpen_interior.uniqueDiffOn;
  · exact uniqueDiffWithinAt_of_mem_nhds ( IsOpen.mem_nhds isOpen_interior hx );
  · intro y hy; simp +decide [ Fin.tail ] ;
    exact hessian_symm f y hy b c;
  · convert hessian_symm f x hx b c using 1

/-
The third derivative is symmetric in the first two arguments.
-/
lemma third_deriv_symm_12 (f : LHSCB V K ν d) (x : V) (hx : x ∈ interior K) (a b c : V) :
    iteratedFDerivWithin ℝ 3 f.f (interior K) x ![a, b, c] =
    iteratedFDerivWithin ℝ 3 f.f (interior K) x ![b, a, c] := by
  rw [ iteratedFDerivWithin_succ_apply_right, iteratedFDerivWithin_succ_apply_right ];
  · rw [ iteratedFDerivWithin_succ_apply_right ];
    · rw [ iteratedFDerivWithin_succ_apply_right, iteratedFDerivWithin_succ_apply_right ];
      · rw [ iteratedFDerivWithin_one_apply ];
        · have h_symm : IsSymmSndFDerivWithinAt ℝ (fun y => fderivWithin ℝ f.f (interior K) y) (interior K) x := by
            apply_rules [ ContDiffWithinAt.isSymmSndFDerivWithinAt ];
            any_goals exact le_rfl;
            · have h_cont_diff : ContDiffOn ℝ 2 (fun y => fderivWithin ℝ f.f (interior K) y) (interior K) := by
                have h_cont_diff : ContDiffOn ℝ 3 f.f (interior K) := by
                  exact f.contDiff₃;
                apply_rules [ ContDiffOn.fderivWithin, h_cont_diff ];
                exact h_cont_diff;
                · exact isOpen_interior.uniqueDiffOn;
                · decide +revert;
              exact h_cont_diff.contDiffWithinAt hx |> ContDiffWithinAt.of_le <| by norm_num [ minSmoothness ] ;
            · exact isOpen_interior.uniqueDiffOn;
            · exact subset_closure ( by simpa using hx );
          convert congr_arg ( fun f => f c ) ( h_symm a b ) using 1;
        · exact uniqueDiffWithinAt_of_mem_nhds ( IsOpen.mem_nhds isOpen_interior hx );
      · exact isOpen_interior.uniqueDiffOn;
      · exact hx;
      · exact isOpen_interior.uniqueDiffOn;
      · exact hx;
    · exact isOpen_interior.uniqueDiffOn;
    · exact hx;
  · exact isOpen_interior.uniqueDiffOn;
  · exact hx;
  · exact isOpen_interior.uniqueDiffOn;
  · exact hx

end ThirdDerivSymmetry

/-! ### Hessian quadratic form properties -/

section HessianProperties

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {K : Set V} {ν : ℕ} {d : ℕ∞}

/-
The Hessian satisfies the parallelogram law.
-/
lemma hess_parallelogram (f : LHSCB V K ν d) (x : V) (hx : x ∈ interior K) (a b : V) :
    iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => a + b) +
    iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => a - b) =
    2 * iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => a) +
    2 * iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => b) := by
  convert congr_arg₂ ( · + · ) ( cmmap2_add_first _ a b _ ) ( cmmap2_sub_first _ a b _ ) using 1 ; ring;
  convert rfl;
  any_goals rename_i i; fin_cases i <;> rfl;
  rw [ cmmap2_add_second, cmmap2_sub_second ] ; ring;
  rw [ cmmap2_add_second, cmmap2_sub_second ] ; ring;
  congr! 2;
  · exact congr_arg _ ( funext fun i => by fin_cases i <;> rfl );
  · exact congr_arg _ ( funext fun i => by fin_cases i <;> rfl )

/-
Scaling property of the Hessian: `H(t • v) = t² * H(v)`.
-/
lemma hess_smul (f : LHSCB V K ν d) (x : V) (hx : x ∈ interior K) (t : ℝ) (v : V) :
    iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => t • v) =
    t ^ 2 * iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => v) := by
  convert ( ContinuousMultilinearMap.map_smul_univ _ _ _ ) using 1;
  all_goals try infer_instance;
  simp +decide [ pow_two, mul_assoc, mul_comm, mul_left_comm, Fin.prod_univ_succ ]

end HessianProperties

/-! ### The 2-1 mixed bound -/

section TwoOneBound

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {K : Set V} {ν : ℕ} {d : ℕ∞}

/-
Cauchy-Schwarz for the Hessian bilinear form: B(u,v)² ≤ H(u)*H(v).
-/
lemma hess_cauchy_schwarz (f : LHSCB V K ν d)
    (x : V) (hx : x ∈ interior K) (u v : V) :
    (iteratedFDerivWithin ℝ 2 f.f (interior K) x ![u, v]) ^ 2 ≤
      iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => u) *
      iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => v) := by
  -- By the properties of the Hessian, we know that $H(u+tv) \geq 0$ for all $t$.
  have h_hessian_nonneg : ∀ t : ℝ, (iteratedFDerivWithin ℝ 2 f.f (interior K) x) ![u + t • v, u + t • v] ≥ 0 := by
    convert f.self_concordant_hessian_nonneg x hx using 1;
    constructor <;> intro h <;> have := h 0 <;> simp_all +decide [ two_smul ];
    · exact?;
    · intro t; convert h ( u + t • v ) using 1;
      convert rfl;
      rename_i i; fin_cases i <;> rfl;
  -- By definition of the Hessian, we know that $H(u + tv) = H(u) + 2tB(u,v) + t^2H(v)$.
  have h_hessian_expand : ∀ t : ℝ, (iteratedFDerivWithin ℝ 2 f.f (interior K) x) ![u + t • v, u + t • v] = (iteratedFDerivWithin ℝ 2 f.f (interior K) x) (fun _ => u) + 2 * t * (iteratedFDerivWithin ℝ 2 f.f (interior K) x) ![u, v] + t^2 * (iteratedFDerivWithin ℝ 2 f.f (interior K) x) (fun _ => v) := by
    intro t
    have h_hessian_expand : (iteratedFDerivWithin ℝ 2 f.f (interior K) x) ![u + t • v, u + t • v] = (iteratedFDerivWithin ℝ 2 f.f (interior K) x) ![u, u] + 2 * t * (iteratedFDerivWithin ℝ 2 f.f (interior K) x) ![u, v] + t^2 * (iteratedFDerivWithin ℝ 2 f.f (interior K) x) ![v, v] := by
      simp +decide only [cmmap2_add_second, cmmap2_add_first, cmmap2_smul_first, cmmap2_smul_second] ; ring;
      rw [ show ( iteratedFDerivWithin ℝ 2 f.f ( interior K ) x ) ![ v, u ] = ( iteratedFDerivWithin ℝ 2 f.f ( interior K ) x ) ![ u, v ] from hessian_symm f x hx v u ] ; ring;
    grind +suggestions;
  by_cases h : ( iteratedFDerivWithin ℝ 2 f.f ( interior K ) x ) ( fun _ => v ) = 0 <;> simp_all +decide [ sq ];
  · contrapose! h_hessian_nonneg;
    exact ⟨ ( - ( ( iteratedFDerivWithin ℝ 2 f.f ( interior K ) x ) fun _ => u ) - 1 ) / ( 2 * ( iteratedFDerivWithin ℝ 2 f.f ( interior K ) x ) ![u, v] ), by nlinarith [ mul_div_cancel₀ ( - ( ( iteratedFDerivWithin ℝ 2 f.f ( interior K ) x ) fun _ => u ) - 1 ) ( by nlinarith : ( 2 * ( iteratedFDerivWithin ℝ 2 f.f ( interior K ) x ) ![u, v] ) ≠ 0 ) ] ⟩;
  · by_cases h₂ : (iteratedFDerivWithin ℝ 2 f.f (interior K) x) (fun _ => v) > 0;
    · nlinarith [ h_hessian_nonneg ( - ( ( iteratedFDerivWithin ℝ 2 f.f ( interior K ) x ) ![ u, v ] ) / ( ( iteratedFDerivWithin ℝ 2 f.f ( interior K ) x ) fun _ => v ) ), mul_div_cancel₀ ( - ( ( iteratedFDerivWithin ℝ 2 f.f ( interior K ) x ) ![ u, v ] ) ) h ];
    · exact False.elim ( h ( le_antisymm ( le_of_not_gt h₂ ) ( f.self_concordant_hessian_nonneg x hx v ) ) )

/-
Expansion of the third derivative along h = u + tv using multilinearity and symmetry.
-/
lemma third_deriv_expand (f : LHSCB V K ν d)
    (x : V) (hx : x ∈ interior K) (u v : V) (t : ℝ) :
    iteratedFDerivWithin ℝ 3 f.f (interior K) x (fun _ => u + t • v) =
      iteratedFDerivWithin ℝ 3 f.f (interior K) x (fun _ => u) +
      3 * t * iteratedFDerivWithin ℝ 3 f.f (interior K) x ![u, u, v] +
      3 * t ^ 2 * iteratedFDerivWithin ℝ 3 f.f (interior K) x ![u, v, v] +
      t ^ 3 * iteratedFDerivWithin ℝ 3 f.f (interior K) x (fun _ => v) := by
  -- Apply the expansion from `h_expansion` to rewrite the left-hand side.
  have h_lhs_expand : (iteratedFDerivWithin ℝ 3 f.f (interior K) x) (fun _ => u + t • v) = (iteratedFDerivWithin ℝ 3 f.f (interior K) x) ![u + t • v, u + t • v, u + t • v] := by
    convert rfl;
    rename_i i; fin_cases i <;> rfl;
  -- Expand the right-hand side using the definitions of `cmmap_add_first`, `cmmap_add_second`, `cmmap_smul_first`, and `cmmap_smul_second`.
  have h_rhs_expand : (iteratedFDerivWithin ℝ 3 f.f (interior K) x) ![u, u + t • v, u + t • v] =
    (iteratedFDerivWithin ℝ 3 f.f (interior K) x) ![u, u, u + t • v] + t * (iteratedFDerivWithin ℝ 3 f.f (interior K) x) ![u, v, u + t • v] := by
      convert cmmap_add_second _ _ _ _ using 1;
      grind +suggestions;
      exact V;
      exact inferInstance;
      exact inferInstance;
      · exact 0;
      · exact u;
      · exact u;
      · exact u;
  have h_rhs_expand2 : (iteratedFDerivWithin ℝ 3 f.f (interior K) x) ![u, u, u + t • v] =
    (iteratedFDerivWithin ℝ 3 f.f (interior K) x) ![u, u, u] + t * (iteratedFDerivWithin ℝ 3 f.f (interior K) x) ![u, u, v] := by
      grind +suggestions;
  have h_rhs_expand3 : (iteratedFDerivWithin ℝ 3 f.f (interior K) x) ![u, v, u + t • v] =
    (iteratedFDerivWithin ℝ 3 f.f (interior K) x) ![u, v, u] + t * (iteratedFDerivWithin ℝ 3 f.f (interior K) x) ![u, v, v] := by
      grind +suggestions;
  have h_rhs_expand4 : (iteratedFDerivWithin ℝ 3 f.f (interior K) x) ![v, u + t • v, u + t • v] =
    (iteratedFDerivWithin ℝ 3 f.f (interior K) x) ![v, u, u + t • v] + t * (iteratedFDerivWithin ℝ 3 f.f (interior K) x) ![v, v, u + t • v] := by
      grind +suggestions;
  have h_rhs_expand5 : (iteratedFDerivWithin ℝ 3 f.f (interior K) x) ![v, u, u + t • v] =
    (iteratedFDerivWithin ℝ 3 f.f (interior K) x) ![v, u, u] + t * (iteratedFDerivWithin ℝ 3 f.f (interior K) x) ![v, u, v] := by
      convert cmmap_add_second _ _ _ _ using 1;
      rotate_left;
      exact V;
      exact inferInstance;
      exact inferInstance;
      exact ( iteratedFDerivWithin ℝ 3 f.f ( interior K ) x );
      exact v;
      exact u;
      exact t • v;
      grind +suggestions;
  have h_rhs_expand6 : (iteratedFDerivWithin ℝ 3 f.f (interior K) x) ![v, v, u + t • v] =
    (iteratedFDerivWithin ℝ 3 f.f (interior K) x) ![v, v, u] + t * (iteratedFDerivWithin ℝ 3 f.f (interior K) x) ![v, v, v] := by
      convert cmmap_add_second _ _ _ _ using 1;
      any_goals exact ℝ;
      any_goals exact t;
      grind +suggestions;
      all_goals try infer_instance;
      exact 0;
  grind +suggestions

/-
Expansion of the Hessian H(u+tv) using bilinearity.
-/
lemma hess_expand (f : LHSCB V K ν d)
    (x : V) (hx : x ∈ interior K) (u v : V) (t : ℝ) :
    iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => u + t • v) =
      iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => u) +
      2 * t * iteratedFDerivWithin ℝ 2 f.f (interior K) x ![u, v] +
      t ^ 2 * iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => v) := by
  rw [ show ( fun _ : Fin 2 => u + t • v ) = ![u + t • v, u + t • v] from by ext i; fin_cases i <;> rfl ];
  have := cmmap2_add_first ( iteratedFDerivWithin ℝ 2 f.f ( interior K ) x ) u ( t • v ) ( u + t • v ) ; have := cmmap2_smul_first ( iteratedFDerivWithin ℝ 2 f.f ( interior K ) x ) t v ( u + t • v ) ; have := cmmap2_add_second ( iteratedFDerivWithin ℝ 2 f.f ( interior K ) x ) u u ( t • v ) ; have := cmmap2_smul_second ( iteratedFDerivWithin ℝ 2 f.f ( interior K ) x ) t u v ; ring_nf at * ; simp_all +decide [ hessian_symm ] ;
  have := cmmap2_add_second ( iteratedFDerivWithin ℝ 2 f.f ( interior K ) x ) v u ( t • v ) ; have := cmmap2_smul_second ( iteratedFDerivWithin ℝ 2 f.f ( interior K ) x ) t v v ; simp_all +decide [ hessian_symm ] ; ring;
  rw [ show ( fun _ : Fin 2 => u ) = ![u, u] from by ext i; fin_cases i <;> rfl ] ; rw [ show ( fun _ : Fin 2 => v ) = ![v, v] from by ext i; fin_cases i <;> rfl ] ; ring;

/-
**Polynomial non-negativity lemma.** If a non-negative polynomial `p(t)² ≤ C` for all `t`,
then `p` is constant. Used for the H(v)=0 degenerate case.
-/
lemma polynomial_bounded_const {a b c C : ℝ}
    (hC : 0 ≤ C)
    (h : ∀ t : ℝ, (a + b * t + c * t ^ 2) ^ 2 ≤ C) :
    b = 0 ∧ c = 0 := by
  by_cases hc : c = 0 <;> by_cases hb : b = 0 <;> simp_all +decide [ sq ];
  · exact False.elim <| hb <| by nlinarith [ h ( - ( a + Real.sqrt ( C + 1 ) ) / b ), h ( - ( a - Real.sqrt ( C + 1 ) ) / b ), Real.sqrt_nonneg ( C + 1 ), Real.mul_self_sqrt ( show 0 ≤ C + 1 by linarith ), mul_div_cancel₀ ( - ( a + Real.sqrt ( C + 1 ) ) ) hb, mul_div_cancel₀ ( - ( a - Real.sqrt ( C + 1 ) ) ) hb ] ;
  · have h_contra : Filter.Tendsto (fun t : ℝ => (a + c * t^2)^2) Filter.atTop Filter.atTop := by
      have h_contra : Filter.Tendsto (fun t : ℝ => a + c * t^2) Filter.atTop Filter.atTop ∨ Filter.Tendsto (fun t : ℝ => a + c * t^2) Filter.atTop Filter.atBot := by
        by_cases hc_pos : 0 < c;
        · exact Or.inl <| Filter.Tendsto.add_atTop tendsto_const_nhds <| Filter.Tendsto.const_mul_atTop hc_pos <| by norm_num;
        · exact Or.inr <| Filter.Tendsto.add_atBot tendsto_const_nhds <| Filter.Tendsto.const_mul_atTop_of_neg ( lt_of_le_of_ne ( le_of_not_gt hc_pos ) hc ) <| by norm_num;
      rcases h_contra with h_contra | h_contra <;> [ exact Filter.tendsto_atTop_atTop.mpr fun x => by rcases Filter.eventually_atTop.mp ( h_contra.eventually_gt_atTop ( x + 1 ) ) with ⟨ t, ht ⟩ ; exact ⟨ t, fun y hy => by nlinarith [ ht y hy ] ⟩ ; ; exact Filter.tendsto_atTop_atTop.mpr fun x => by rcases Filter.eventually_atTop.mp ( h_contra.eventually_lt_atBot ( -x - 1 ) ) with ⟨ t, ht ⟩ ; exact ⟨ t, fun y hy => by nlinarith [ ht y hy ] ⟩ ] ;
    exact absurd ( h_contra.eventually_gt_atTop C ) fun H => by obtain ⟨ t, ht ⟩ := H.exists; specialize h t; ring_nf at *; nlinarith;
  · -- Since $c \neq 0$, consider the limit of the polynomial as $t \to \infty$.
    have h_lim_inf : Filter.Tendsto (fun t : ℝ => (a + b * t + c * t ^ 2)) Filter.atTop Filter.atTop ∨ Filter.Tendsto (fun t : ℝ => (a + b * t + c * t ^ 2)) Filter.atTop Filter.atBot := by
      by_cases hc_pos : 0 < c;
      · exact Or.inl <| Filter.tendsto_atTop_atTop.2 fun x => ⟨ |x - a| / c + |b| / c + 1, fun t ht => by cases abs_cases ( x - a ) <;> cases abs_cases b <;> nlinarith [ mul_div_cancel₀ ( |x - a| ) hc, mul_div_cancel₀ ( |b| ) hc, mul_le_mul_of_nonneg_left ht hc_pos.le ] ⟩;
      · by_cases hc_neg : c < 0;
        · rw [ Filter.tendsto_atTop_atBot ];
          exact Or.inr fun x => ⟨ |x - a| / ( -c ) + |b| / ( -c ) + 1, fun t ht => by cases abs_cases ( x - a ) <;> cases abs_cases b <;> nlinarith [ mul_div_cancel₀ ( |x - a| ) ( by linarith : ( -c ) ≠ 0 ), mul_div_cancel₀ ( |b| ) ( by linarith : ( -c ) ≠ 0 ), mul_le_mul_of_nonneg_left ht ( sub_nonneg.mpr hc_neg.le ) ] ⟩;
        · cases lt_or_gt_of_ne hc <;> contradiction;
    rcases h_lim_inf with h_lim_inf | h_lim_inf <;> simp_all +decide [ sq ];
    · exact absurd ( h_lim_inf.eventually_gt_atTop ( C + 1 ) ) fun H => by obtain ⟨ t, ht ⟩ := H.exists; nlinarith [ h t ] ;
    · have := h_lim_inf.eventually ( Filter.eventually_lt_atBot ( -Real.sqrt C ) ) ; obtain ⟨ t, ht ⟩ := this.exists; nlinarith [ h t, Real.sqrt_nonneg C, Real.sq_sqrt hC ] ;

/-
**2-1 bound, degenerate case H(u) = 0**: T(u,u,v) = 0.
-/
lemma sc_two_one_hu_zero (f : LHSCB V K ν d)
    (x : V) (hx : x ∈ interior K) (u v : V)
    (hu : iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => u) = 0) :
    iteratedFDerivWithin ℝ 3 f.f (interior K) x ![u, u, v] = 0 := by
  -- By the polynomial boundedness of the SC inequality, we have $T(u+tv, u+tv, u+tv)^2 \leq 4(yu^2+2*sinuv+xv^2)^3$ for all $t \in \mathbb{R}$.
  have h_poly_bound : ∀ t : ℝ, (iteratedFDerivWithin ℝ 3 f.f (interior K) x (fun _ => u + t • v)) ^ 2 ≤ 4 * (iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => u + t • v)) ^ 3 := by
    exact fun t => f.self_concordant x hx ( u + t • v );
  -- By the polynomial expansion, we have $T(u+tv, u+tv, u+tv) = 3t\beta + 3t^2\gamma + t^3\delta$ and $H(u+tv) = t^2H(v)$.
  have h_expand : ∀ t : ℝ, (iteratedFDerivWithin ℝ 3 f.f (interior K) x (fun _ => u + t • v)) = 3 * t * (iteratedFDerivWithin ℝ 3 f.f (interior K) x ![u, u, v]) + 3 * t ^ 2 * (iteratedFDerivWithin ℝ 3 f.f (interior K) x ![u, v, v]) + t ^ 3 * (iteratedFDerivWithin ℝ 3 f.f (interior K) x (fun _ => v)) := by
    intro t;
    convert third_deriv_expand f x hx u v t using 1;
    have := f.self_concordant x hx u; simp_all +decide [ vec3_const_eq ] ;
  -- By the polynomial expansion, we have $H(u+tv) = t^2H(v)$.
  have h_hessian_expand : ∀ t : ℝ, (iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => u + t • v)) = t ^ 2 * (iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => v)) := by
    intro t
    have h_hessian_expand_step : (iteratedFDerivWithin ℝ 2 f.f (interior K) x ![u, v]) = 0 := by
      have := hess_cauchy_schwarz f x hx u v; simp_all +decide [ sq ] ;
      exact mul_self_eq_zero.mp ( le_antisymm this ( mul_self_nonneg _ ) );
    have := hess_expand f x hx u v t; aesop;
  -- By dividing both sides of the inequality by $t^2$ (for $t \neq 0$), we get $(3\beta + 3t\gamma + t^2\delta)^2 \leq 4t^4H(v)^3$.
  have h_div : ∀ t : ℝ, t ≠ 0 → (3 * (iteratedFDerivWithin ℝ 3 f.f (interior K) x ![u, u, v]) + 3 * t * (iteratedFDerivWithin ℝ 3 f.f (interior K) x ![u, v, v]) + t ^ 2 * (iteratedFDerivWithin ℝ 3 f.f (interior K) x (fun _ => v))) ^ 2 ≤ 4 * t ^ 4 * (iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => v)) ^ 3 := by
    intro t ht
    specialize h_poly_bound t
    rw [h_expand t, h_hessian_expand t] at h_poly_bound
    exact (by
    nlinarith [ mul_self_pos.2 ht ]);
  -- By taking the limit as $t \to 0$, we get $9\beta^2 \leq 0$, hence $\beta = 0$.
  have h_limit : Filter.Tendsto (fun t : ℝ => (3 * (iteratedFDerivWithin ℝ 3 f.f (interior K) x ![u, u, v]) + 3 * t * (iteratedFDerivWithin ℝ 3 f.f (interior K) x ![u, v, v]) + t ^ 2 * (iteratedFDerivWithin ℝ 3 f.f (interior K) x (fun _ => v))) ^ 2) (nhdsWithin 0 {0}ᶜ) (nhds (9 * (iteratedFDerivWithin ℝ 3 f.f (interior K) x ![u, u, v]) ^ 2)) := by
    exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ ( by ring ) );
  have h_limit_zero : Filter.Tendsto (fun t : ℝ => 4 * t ^ 4 * (iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => v)) ^ 3) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ ( by norm_num ) );
  exact sq_eq_zero_iff.mp ( by nlinarith [ le_of_tendsto_of_tendsto h_limit h_limit_zero ( Filter.eventually_of_mem self_mem_nhdsWithin fun t ht => h_div t ht ) ] )

/-
**2-1 bound, degenerate case H(v) = 0**: T(u,u,v) = 0.
-/
lemma sc_two_one_hv_zero (f : LHSCB V K ν d)
    (x : V) (hx : x ∈ interior K) (u v : V)
    (hv : iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => v) = 0) :
    iteratedFDerivWithin ℝ 3 f.f (interior K) x ![u, u, v] = 0 := by
  -- Let $a = T(u,u,u)$, $b = 3T(u,u,v)$, $c = 3T(u,v,v)$.
  set a := iteratedFDerivWithin ℝ 3 f.f (interior K) x ![u, u, u]
  set b := 3 * iteratedFDerivWithin ℝ 3 f.f (interior K) x ![u, u, v]
  set c := 3 * iteratedFDerivWithin ℝ 3 f.f (interior K) x ![u, v, v];
  -- By the SC inequality at $u + tv$, we have $(a + b*t + c*t^2)^2 \leq 4*H(u)^3$ for all $t$.
  have h_sc : ∀ t : ℝ, (a + b * t + c * t ^ 2) ^ 2 ≤ 4 * (iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => u)) ^ 3 := by
    intro t
    have h_T : iteratedFDerivWithin ℝ 3 f.f (interior K) x (fun _ => u + t • v) = a + b * t + c * t ^ 2 := by
      convert third_deriv_expand f x hx u v t using 1 ; ring!;
      rw [ show ( iteratedFDerivWithin ℝ 3 f.f ( interior K ) x ) ( fun _ => v ) = 0 from ?_ ] ; ring!;
      · rw [ show ( fun _ => u : Fin 3 → V ) = ![u, u, u] from by ext i; fin_cases i <;> rfl ] ; ring!;
      · have := f.self_concordant x hx v; aesop;
    have h_H : iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => u + t • v) = iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => u) := by
      have h_H : iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => u + t • v) = iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => u) + 2 * t * iteratedFDerivWithin ℝ 2 f.f (interior K) x ![u, v] + t ^ 2 * iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => v) := by
        convert hess_expand f x hx u v t using 1;
      have h_B : iteratedFDerivWithin ℝ 2 f.f (interior K) x ![u, v] ^ 2 ≤ iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => u) * iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => v) := by
        apply hess_cauchy_schwarz f x hx u v;
      aesop
    have h_SC : (iteratedFDerivWithin ℝ 3 f.f (interior K) x (fun _ => u + t • v)) ^ 2 ≤ 4 * (iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => u + t • v)) ^ 3 := by
      exact f.self_concordant x hx ( u + t • v ) |> fun h => by simpa [ vec3_const_eq ] using h;
    rw [h_T, h_H] at h_SC
    exact h_SC;
  have := polynomial_bounded_const ( show 0 ≤ 4 * ( iteratedFDerivWithin ℝ 2 f.f ( interior K ) x fun _ => u ) ^ 3 by exact mul_nonneg zero_le_four ( pow_nonneg ( f.self_concordant_hessian_nonneg x hx u ) _ ) ) h_sc; aesop;

/-- **2-1 bound, non-degenerate case**: |T(u,u,v)| ≤ 2*H(u)*√H(v) when H(u) > 0, H(v) > 0.

**Strategy.** Set `α := H(u), γ := H(v), β := 2·H(u,v)`, and
`T₀ := T(u)³, T₁ := T(u,u,v), T₂ := T(u,v,v), T₃ := T(v)³`. The
squared SC at the variable direction `u + s·v` gives, by
`third_deriv_expand` and `hess_expand`, the polynomial inequality

  `(T₀ + 3T₁·s + 3T₂·s² + T₃·s³)² ≤ 4·(α + β·s + γ·s²)³`   for all s ∈ ℝ

and `hess_cauchy_schwarz` gives `β² ≤ 4·α·γ`.

The bipolarized bound `T₁² ≤ 4·α²·γ`, equivalently `|T₁| ≤ 2·α·√γ`,
is the canonical hard step of polarized self-concordance theory
(Nesterov–Nemirovski §2.1, Renegar Cor 2.3.4). It is provable in the
saturated case (`T₀² = 4·α³`) via the polynomial root argument
(`R(0) = 0` forces `R'(0) = 0`, giving `T₀·T₁ = 2·α²·β`, hence
`T₁² = α·β² ≤ 4·α²·γ` by CS).

The non-saturated case (`T₀² < 4·α³`) requires either:
* Hilbert SOS coefficient extraction (PSD Hankel matrix chaining), or
* A continuity / scaling-to-saturate argument.

Neither has been closed in Lean. -/
lemma sc_two_one_nondegenerate (f : LHSCB V K ν d)
    (x : V) (hx : x ∈ interior K) (u v : V)
    (hu : 0 < iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => u))
    (hv : 0 < iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => v)) :
    |iteratedFDerivWithin ℝ 3 f.f (interior K) x ![u, u, v]| ≤
      2 * iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => u) *
        Real.sqrt (iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => v)) := by
  sorry

/-- **The 2-1 mixed bound.** `|D³f(x)[u, u, v]| ≤ 2 * H(u) * √H(v)`. -/
lemma sc_two_one_bound (f : LHSCB V K ν d)
    (x : V) (hx : x ∈ interior K) (u v : V) :
    |iteratedFDerivWithin ℝ 3 f.f (interior K) x ![u, u, v]| ≤
      2 * iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => u) *
        Real.sqrt (iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => v)) := by
  by_cases hu : iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => u) = 0
  · rw [sc_two_one_hu_zero f x hx u v hu]
    simp [abs_of_nonneg, mul_nonneg, Real.sqrt_nonneg,
          f.self_concordant_hessian_nonneg x hx u]
  · by_cases hv : iteratedFDerivWithin ℝ 2 f.f (interior K) x (fun _ => v) = 0
    · rw [sc_two_one_hv_zero f x hx u v hv]
      simp only [abs_zero, hv, Real.sqrt_zero, mul_zero]
      exact le_refl _
    · exact sc_two_one_nondegenerate f x hx u v
        (lt_of_le_of_ne (f.self_concordant_hessian_nonneg x hx u) (Ne.symm hu))
        (lt_of_le_of_ne (f.self_concordant_hessian_nonneg x hx v) (Ne.symm hv))

end TwoOneBound

end Irn