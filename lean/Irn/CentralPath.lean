/-
# Central Path (paper §2.2–§3.2)

The central-path map `T_μ : Cplus → H`, the central-path point at
level `μ`, existence and uniqueness (Theorem 5), and smoothness in `μ`
(Theorem 6).

Paper references:
* Definition 3 (central path)
* Proposition 3 (sphericity) → `centralPath_norm_sq`
* Theorem 5 (existence and uniqueness)
* Theorem 6 (smoothness)
-/

import Irn.Setting
import Irn.Monotone
import Mathlib.Analysis.Calculus.ContDiff.Defs

namespace Irn

open scoped InnerProductSpace

namespace IrnSetup

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  (𝓢 : IrnSetup X Y)

/-- The central-path map `T_μ(u) = Q(u) + μ u + μ φ(u)`. -/
noncomputable def T (μ : ℝ) (u : H X Y) : H X Y :=
  𝓢.Q u + μ • u + μ • 𝓢.φ u

/-- `u` is a central-path point at level `μ` if `u ∈ int C` and
`T_μ(u) = 0`. -/
def IsCentralPathPoint (μ : ℝ) (u : H X Y) : Prop :=
  u ∈ 𝓢.C_interior ∧ 𝓢.T μ u = 0

/-- **Proposition 3 (Sphericity).** Every central-path point lies on
the sphere of radius `r = √(ν+1)`. -/
theorem centralPath_norm_sq {μ : ℝ} (hμ : 0 < μ) {u : H X Y}
    (h : 𝓢.IsCentralPathPoint μ u) :
    ‖u‖ ^ 2 = (𝓢.ν : ℝ) + 1 := by
  obtain ⟨hC, hT⟩ := h
  have key : inner ℝ u (𝓢.T μ u) = (0 : ℝ) := by
    rw [hT]; exact inner_zero_right _
  unfold T at key
  rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
      𝓢.inner_u_Q (𝓢.C_interior_subset_Cplus hC), 𝓢.inner_u_phi u hC,
      real_inner_self_eq_norm_sq] at key
  nlinarith [key, hμ]

/-- `T_μ` is strictly monotone on `C_interior` for `μ > 0`. This is the
key monotonicity fact: `T_μ = Q + μ•id + μ•φ`, where `Q` is monotone
(`Q_monotone`), `μ•id` is strictly monotone (`μ > 0`), and `μ•φ` is
monotone (`phi_monotone`). The sum (mono + strict + mono) is strictly
monotone. -/
theorem T_strictMonotoneOn (μ : ℝ) (hμ : 0 < μ) :
    IsStrictMonotoneOn (𝓢.T μ) 𝓢.C_interior := by
  intro u hu v hv huv
  have h_expand : 𝓢.T μ u - 𝓢.T μ v =
      (𝓢.Q u - 𝓢.Q v) + μ • (u - v) + μ • (𝓢.φ u - 𝓢.φ v) := by
    unfold T; rw [smul_sub, smul_sub]; abel
  rw [h_expand, inner_add_right, inner_add_right, inner_smul_right,
      inner_smul_right, real_inner_self_eq_norm_sq]
  have h_Q := 𝓢.Q_monotone u (𝓢.C_interior_subset_Cplus hu) v
    (𝓢.C_interior_subset_Cplus hv)
  have h_phi := 𝓢.phi_monotone u hu v hv
  have h_norm_pos : 0 < ‖u - v‖ ^ 2 := by
    have : 0 < ‖u - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr huv)
    positivity
  have h_mu_norm : 0 < μ * ‖u - v‖ ^ 2 := mul_pos hμ h_norm_pos
  have h_mu_phi : 0 ≤ μ * inner ℝ (u - v) (𝓢.φ u - 𝓢.φ v) :=
    mul_nonneg hμ.le h_phi
  linarith

/-- **Uniqueness of the central-path point.** Two central-path points
at the same `μ > 0` are equal. Immediate from strict monotonicity of
`T_μ`: if `T_μ u = T_μ v = 0` and `u ≠ v`, then
`0 < ⟨u-v, T_μ u - T_μ v⟩ = ⟨u-v, 0⟩ = 0`, contradiction. -/
theorem unique_centralPath (μ : ℝ) (hμ : 0 < μ)
    {u v : H X Y} (hu : 𝓢.IsCentralPathPoint μ u)
    (hv : 𝓢.IsCentralPathPoint μ v) : u = v := by
  obtain ⟨hC_u, hT_u⟩ := hu
  obtain ⟨hC_v, hT_v⟩ := hv
  by_contra huv
  have h_strict := 𝓢.T_strictMonotoneOn μ hμ u hC_u v hC_v huv
  rw [hT_u, hT_v, sub_self, inner_zero_right] at h_strict
  exact lt_irrefl 0 h_strict

/-- `f_lhscb.grad` is continuous on `interior K_f_lifted` (from C³). -/
theorem f_lhscb_grad_continuousOn :
    ContinuousOn 𝓢.f_lhscb.grad (interior 𝓢.K_f_lifted) := by
  -- f_lhscb.grad u = (toDual_H).symm (fderiv ℝ f_lhscb.f u)
  have h_fderiv_within_C2 :
      ContDiffOn ℝ 2 (fderivWithin ℝ 𝓢.f_lhscb.f (interior 𝓢.K_f_lifted))
        (interior 𝓢.K_f_lifted) := by
    have := 𝓢.f_lhscb.contDiff.fderivWithin
      isOpen_interior.uniqueDiffOn (m := 2) (by norm_num)
    simpa using this
  have h_fderiv_C2 :
      ContDiffOn ℝ 2 (fderiv ℝ 𝓢.f_lhscb.f) (interior 𝓢.K_f_lifted) :=
    h_fderiv_within_C2.congr
      (fun y hy => (fderivWithin_of_isOpen isOpen_interior hy).symm)
  show ContinuousOn (fun u =>
      (InnerProductSpace.toDual ℝ (H X Y)).symm (fderiv ℝ 𝓢.f_lhscb.f u))
        (interior 𝓢.K_f_lifted)
  exact (InnerProductSpace.toDual ℝ (H X Y)).symm.continuous.comp_continuousOn
    h_fderiv_C2.continuousOn

/-- `φ` is continuous on `C_interior`: sum of `f_lhscb.grad` (continuous
on `interior K_f_lifted ⊇ C_interior`) and `(-1/τ) • e_τ` (continuous
where `τ ≠ 0`, i.e., on `Cplus ⊇ C_interior`). -/
theorem phi_continuousOn : ContinuousOn 𝓢.φ 𝓢.C_interior := by
  unfold φ
  apply ContinuousOn.add
  · -- f_lhscb.grad on C_interior ⊆ interior K_f_lifted
    apply 𝓢.f_lhscb_grad_continuousOn.mono
    exact 𝓢.C_interior_subset_f_lhscb_interior
  · -- (-1 / tau_proj u) • e_τ on C_interior
    apply ContinuousOn.smul _ continuousOn_const
    apply ContinuousOn.div continuousOn_const
      𝓢.tau_proj_continuous.continuousOn
    intro u hu
    exact ne_of_gt hu.2

/-- `Q` is continuous on `C_interior`: `M_clm` (continuous CLM) minus
`(Px_bilinform(x, x) / τ) • e_τ` (continuous on `Cplus`). -/
theorem Q_continuousOn : ContinuousOn 𝓢.Q 𝓢.C_interior := by
  show ContinuousOn (fun u =>
    𝓢.M_apply u -
      (𝓢.Px_bilinform (𝓢.x_proj u) (𝓢.x_proj u) / 𝓢.tau_proj u) •
        𝓢.e_τ) 𝓢.C_interior
  apply ContinuousOn.sub
  · -- M_apply = M_clm (CLM)
    exact (𝓢.M_clm.continuous).continuousOn
  · -- (Px(x,x) / τ) • e_τ
    apply ContinuousOn.smul _ continuousOn_const
    apply ContinuousOn.div
    · -- Px_bilinform(x_proj u, x_proj u) is continuous in u
      show ContinuousOn (fun u => 𝓢.Px_bilinform (𝓢.x_proj u) (𝓢.x_proj u)) _
      unfold Px_bilinform
      -- inner (x_proj u) (P (x_proj u)) — continuous
      have h_xproj : Continuous 𝓢.x_proj := by
        show Continuous fun u : H X Y => u.fst
        fun_prop
      have h_inner :
          Continuous (fun u : H X Y => inner ℝ (𝓢.x_proj u) (𝓢.P (𝓢.x_proj u))) := by
        apply Continuous.inner h_xproj
        exact 𝓢.P.continuous.comp h_xproj
      exact h_inner.continuousOn
    · exact 𝓢.tau_proj_continuous.continuousOn
    · intro u hu
      exact ne_of_gt hu.2

/-- `T_μ` is continuous on `C_interior`. -/
theorem T_continuousOn (μ : ℝ) : ContinuousOn (𝓢.T μ) 𝓢.C_interior := by
  unfold T
  apply ContinuousOn.add
  apply ContinuousOn.add
  · exact 𝓢.Q_continuousOn
  · exact (continuous_const.smul continuous_id).continuousOn
  · exact (continuousOn_const).smul 𝓢.phi_continuousOn

/-- `C_interior` is convex (intersection of `interior K_f_lifted` (convex
via `Convex.linear_preimage`) and `Cplus = {τ > 0}` (convex via
`convex_Ioi`)). -/
theorem C_interior_convex : Convex ℝ 𝓢.C_interior := by
  show Convex ℝ {u : H X Y | 𝓢.y_proj u ∈ interior (𝓢.K : Set Y) ∧
                              0 < 𝓢.tau_proj u}
  have h1 : Convex ℝ {u : H X Y | 𝓢.y_proj u ∈ interior (𝓢.K : Set Y)} :=
    (𝓢.K.convex.interior).linear_preimage
      (IrnSetup.y_proj_linear : H X Y →L[ℝ] Y).toLinearMap
  have h2 : Convex ℝ {u : H X Y | 0 < 𝓢.tau_proj u} :=
    (convex_Ioi (0:ℝ)).linear_preimage
      (IrnSetup.tau_proj_linear : H X Y →L[ℝ] ℝ).toLinearMap
  exact h1.inter h2

/-- `C_interior` is non-empty: pick any `y₀ ∈ interior K` from the
`K_interior_nonempty` Slater hypothesis and form `u₀ = (0, y₀, 1)`. -/
theorem C_interior_nonempty : 𝓢.C_interior.Nonempty := by
  obtain ⟨y₀, hy₀⟩ := 𝓢.K_interior_nonempty
  refine ⟨WithLp.toLp 2 ((0 : X), WithLp.toLp 2 (y₀, (1 : ℝ))), ?_, ?_⟩
  · show 𝓢.y_proj _ ∈ interior (𝓢.K : Set Y)
    exact hy₀
  · show (0 : ℝ) < 𝓢.tau_proj _
    exact zero_lt_one

/-- `C_interior` is open. -/
theorem C_interior_isOpen : IsOpen 𝓢.C_interior := by
  show IsOpen {u : H X Y | 𝓢.y_proj u ∈ interior (𝓢.K : Set Y) ∧
                            0 < 𝓢.tau_proj u}
  have h1 : IsOpen {u : H X Y | 𝓢.y_proj u ∈ interior (𝓢.K : Set Y)} :=
    isOpen_interior.preimage 𝓢.y_proj_continuous
  have h2 : IsOpen {u : H X Y | 0 < 𝓢.tau_proj u} :=
    isOpen_Ioi.preimage 𝓢.tau_proj_continuous
  exact h1.inter h2

/-- `‖e_τ‖ = 1`. The τ-direction unit vector is a unit vector. -/
lemma e_tau_norm : ‖(𝓢.e_τ : H X Y)‖ = 1 := by
  have h_sq : ‖(𝓢.e_τ : H X Y)‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, 𝓢.inner_u_e_tau]
    show 𝓢.e_τ.snd.snd = 1
    rfl
  have h_nn : 0 ≤ ‖(𝓢.e_τ : H X Y)‖ := norm_nonneg _
  nlinarith [h_sq, h_nn]

/-- The τ-component of `f_lhscb.grad u` is zero: `f_lhscb.f` depends
only on the y-block (`f_lhscb.f u = fBarrier.f (y_proj u)`), so its
gradient lifts as `(0, ∇fBarrier(y_proj u), 0)`. -/
lemma inner_f_lhscb_grad_e_tau (u : H X Y) (hu : u ∈ interior 𝓢.K_f_lifted) :
    inner ℝ (𝓢.f_lhscb.grad u) 𝓢.e_τ = (0 : ℝ) := by
  show inner ℝ ((InnerProductSpace.toDual ℝ (H X Y)).symm
        (fderiv ℝ 𝓢.f_lhscb.f u)) 𝓢.e_τ = 0
  rw [InnerProductSpace.toDual_symm_apply]
  -- Chain rule: f_lhscb.f = fBarrier.f ∘ y_proj_linear.
  have hy_int : 𝓢.y_proj u ∈ interior (𝓢.K : Set Y) := by
    rw [𝓢.interior_K_f_lifted] at hu; exact hu
  have h_fb_diffAt : DifferentiableAt ℝ 𝓢.fBarrier.f (𝓢.y_proj u) :=
    (𝓢.fBarrier.contDiff.differentiableOn (by norm_num)).differentiableAt
      (isOpen_interior.mem_nhds hy_int)
  have h_yp_hd : HasFDerivAt (fun v : H X Y => 𝓢.y_proj v)
      (IrnSetup.y_proj_linear : H X Y →L[ℝ] Y) u :=
    (IrnSetup.y_proj_linear : H X Y →L[ℝ] Y).hasFDerivAt
  have h_comp : HasFDerivAt 𝓢.f_lhscb.f
      ((fderiv ℝ 𝓢.fBarrier.f (𝓢.y_proj u)).comp
        (IrnSetup.y_proj_linear : H X Y →L[ℝ] Y)) u :=
    h_fb_diffAt.hasFDerivAt.comp u h_yp_hd
  rw [h_comp.fderiv]
  show (fderiv ℝ 𝓢.fBarrier.f (𝓢.y_proj u))
        ((IrnSetup.y_proj_linear : H X Y →L[ℝ] Y) 𝓢.e_τ) = 0
  have h_yp_eτ : (IrnSetup.y_proj_linear : H X Y →L[ℝ] Y) 𝓢.e_τ = 0 := by
    show 𝓢.y_proj 𝓢.e_τ = 0
    rfl
  rw [h_yp_eτ, ContinuousLinearMap.map_zero]

/-- `T_μ` is boundary-coercive on `C_interior` for `μ > 0`.

**Case A (`tau_proj x = 0`):** The τ-component of `T_μ u` is
`M_apply.τ + μτ − (Px(x,x) + μ)/τ`. As `τ → 0+`, this `→ -∞` (the
`-(Px+μ)/τ` term dominates since `Px ≥ 0` and `μ > 0`). Hence
`|τ-component of T_μ u| → ∞`, and `‖T_μ u‖ ≥ |τ-component|`.

**Case B (`tau_proj x > 0`, hence `y_proj x ∈ frontier K`):** Apply
`f_lhscb.grad_norm_tendsto_atTop` to get `‖μ • f_lhscb.grad u‖ → ∞`.
Combined with `R u := Q u + μu − (μ/τ)•e_τ` continuous (hence bounded)
near `x` (since `τ` stays positive), reverse triangle on
`T u = R u + μ • f_lhscb.grad u` gives `‖T u‖ ≥ μ‖∇f‖ − ‖R u‖ → ∞`. -/
theorem T_coercive (μ : ℝ) (hμ : 0 < μ) :
    ∀ x ∈ frontier 𝓢.C_interior,
      Filter.Tendsto (fun u => ‖𝓢.T μ u‖) (nhdsWithin x 𝓢.C_interior)
        Filter.atTop := by
  intro x hx
  have h_etau_norm := 𝓢.e_tau_norm
  -- `x ∈ closure C_interior` and `x ∉ C_interior` (since `C_interior` is open).
  have h_x_cl : x ∈ closure 𝓢.C_interior := hx.1
  have h_x_notC : x ∉ 𝓢.C_interior := by
    have h_int : interior 𝓢.C_interior = 𝓢.C_interior :=
      𝓢.C_interior_isOpen.interior_eq
    have := hx.2
    rwa [h_int] at this
  -- `tau_proj x ≥ 0` (from `closure {τ > 0} ⊆ {τ ≥ 0}`).
  have h_tau_x_nn : 0 ≤ 𝓢.tau_proj x := by
    have h_subset : closure 𝓢.C_interior ⊆ {u | 0 ≤ 𝓢.tau_proj u} := by
      refine closure_minimal ?_ ?_
      · intro u hu; exact le_of_lt hu.2
      · exact isClosed_Ici.preimage 𝓢.tau_proj_continuous
    exact h_subset h_x_cl
  -- Continuity of `tau_proj ∘ M_apply`.
  have h_M_cont : Continuous (fun u : H X Y => 𝓢.tau_proj (𝓢.M_apply u)) :=
    𝓢.tau_proj_continuous.comp 𝓢.M_clm.continuous
  by_cases h_tau_zero : 𝓢.tau_proj x = 0
  · -- **CASE A:** τ_x = 0. The τ-component of `T_μ u` tends to `-∞`.
    have h_tau_to_zero_pos :
        Filter.Tendsto 𝓢.tau_proj (nhdsWithin x 𝓢.C_interior)
          (nhdsWithin 0 (Set.Ioi 0)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h := 𝓢.tau_proj_continuous.tendsto x
        rw [h_tau_zero] at h
        exact h.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with u hu; exact hu.2
    -- `μ / τ_u → +∞`.
    have h_mu_div : Filter.Tendsto (fun u : H X Y => μ / 𝓢.tau_proj u)
        (nhdsWithin x 𝓢.C_interior) Filter.atTop := by
      have h_R : Filter.Tendsto (fun τ : ℝ => μ / τ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atTop := by
        have h_inv : Filter.Tendsto (fun τ : ℝ => τ⁻¹)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atTop :=
          tendsto_inv_nhdsGT_zero
        have h_mul := h_inv.const_mul_atTop hμ
        refine h_mul.congr ?_
        intro τ; show μ * τ⁻¹ = μ / τ; ring
      exact h_R.comp h_tau_to_zero_pos
    -- The bounded part `-μ τ_u - tau_proj M_u` tends to a constant.
    have h_bdd_tendsto : Filter.Tendsto
        (fun u : H X Y => -μ * 𝓢.tau_proj u - 𝓢.tau_proj (𝓢.M_apply u))
        (nhdsWithin x 𝓢.C_interior)
        (nhds (-μ * 𝓢.tau_proj x - 𝓢.tau_proj (𝓢.M_apply x))) := by
      refine (Continuous.tendsto ?_ x).mono_left nhdsWithin_le_nhds
      exact (continuous_const.mul 𝓢.tau_proj_continuous).sub h_M_cont
    -- Combine: `μ/τ_u + (-μ τ_u - tau_proj M_u) → +∞`.
    have h_lower_atTop : Filter.Tendsto
        (fun u : H X Y =>
          μ / 𝓢.tau_proj u - μ * 𝓢.tau_proj u - 𝓢.tau_proj (𝓢.M_apply u))
        (nhdsWithin x 𝓢.C_interior) Filter.atTop := by
      have h_sum := h_mu_div.atTop_add h_bdd_tendsto
      refine h_sum.congr ?_; intro u; ring
    -- Eventually: `lower ≤ ‖T_μ u‖`.
    have h_eventually_le : ∀ᶠ u in nhdsWithin x 𝓢.C_interior,
        μ / 𝓢.tau_proj u - μ * 𝓢.tau_proj u - 𝓢.tau_proj (𝓢.M_apply u) ≤
          ‖𝓢.T μ u‖ := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      have hτu : 0 < 𝓢.tau_proj u := hu.2
      have hτu_ne : 𝓢.tau_proj u ≠ 0 := ne_of_gt hτu
      -- `⟨T_μ u, e_τ⟩` explicit formula.
      have h_T_etau : inner ℝ (𝓢.T μ u) 𝓢.e_τ =
          𝓢.tau_proj (𝓢.M_apply u) -
            𝓢.Px_bilinform (𝓢.x_proj u) (𝓢.x_proj u) / 𝓢.tau_proj u +
            μ * 𝓢.tau_proj u - μ / 𝓢.tau_proj u := by
        show inner ℝ (𝓢.Q u + μ • u + μ • 𝓢.φ u) 𝓢.e_τ = _
        rw [inner_add_left, inner_add_left, real_inner_smul_left,
            real_inner_smul_left]
        have h_tau_etau : 𝓢.tau_proj 𝓢.e_τ = (1 : ℝ) := rfl
        have h_Q_etau : inner ℝ (𝓢.Q u) 𝓢.e_τ =
            𝓢.tau_proj (𝓢.M_apply u) -
              𝓢.Px_bilinform (𝓢.x_proj u) (𝓢.x_proj u) / 𝓢.tau_proj u := by
          show inner ℝ
              (𝓢.M_apply u -
                (𝓢.Px_bilinform (𝓢.x_proj u) (𝓢.x_proj u) / 𝓢.tau_proj u) •
                  𝓢.e_τ) 𝓢.e_τ = _
          rw [inner_sub_left, real_inner_smul_left, 𝓢.inner_u_e_tau,
              𝓢.inner_u_e_tau, h_tau_etau]
          ring
        have h_phi_etau : inner ℝ (𝓢.φ u) 𝓢.e_τ = -1 / 𝓢.tau_proj u := by
          show inner ℝ
              (𝓢.f_lhscb.grad u + (-1 / 𝓢.tau_proj u) • 𝓢.e_τ) 𝓢.e_τ = _
          rw [inner_add_left, real_inner_smul_left,
              𝓢.inner_f_lhscb_grad_e_tau u
                (𝓢.C_interior_subset_f_lhscb_interior hu),
              𝓢.inner_u_e_tau, h_tau_etau]
          ring
        rw [h_Q_etau, 𝓢.inner_u_e_tau, h_phi_etau]
        ring
      have h_Px_nn : 0 ≤ 𝓢.Px_bilinform (𝓢.x_proj u) (𝓢.x_proj u) :=
        𝓢.Px_bilinform_self_nonneg _
      have h_Px_div_nn :
          0 ≤ 𝓢.Px_bilinform (𝓢.x_proj u) (𝓢.x_proj u) / 𝓢.tau_proj u :=
        div_nonneg h_Px_nn hτu.le
      have h_cs : |inner ℝ (𝓢.T μ u) 𝓢.e_τ| ≤ ‖𝓢.T μ u‖ * ‖𝓢.e_τ‖ :=
        abs_real_inner_le_norm _ _
      rw [h_etau_norm, mul_one] at h_cs
      have h_neg_le : -inner ℝ (𝓢.T μ u) 𝓢.e_τ ≤ ‖𝓢.T μ u‖ := by
        have := abs_le.mp h_cs; linarith
      linarith [h_T_etau, h_Px_div_nn, h_neg_le]
    exact Filter.tendsto_atTop_mono' _ h_eventually_le h_lower_atTop
  · -- **CASE B:** τ_x > 0, so `y_proj x ∈ frontier K`.
    have h_tau_x_pos : 0 < 𝓢.tau_proj x :=
      lt_of_le_of_ne h_tau_x_nn (Ne.symm h_tau_zero)
    -- `y_proj x ∈ frontier K`.
    have h_yp_x_cl : 𝓢.y_proj x ∈ closure (𝓢.K : Set Y) := by
      have h_subset : closure 𝓢.C_interior ⊆ 𝓢.y_proj ⁻¹' closure (𝓢.K : Set Y) := by
        refine closure_minimal ?_ ?_
        · intro u hu
          exact subset_closure (interior_subset hu.1)
        · exact isClosed_closure.preimage 𝓢.y_proj_continuous
      exact h_subset h_x_cl
    have h_yp_x_in_K : 𝓢.y_proj x ∈ (𝓢.K : Set Y) := by
      have h_K_closed : IsClosed (𝓢.K : Set Y) := 𝓢.K.isClosed
      rwa [h_K_closed.closure_eq] at h_yp_x_cl
    have h_yp_x_not_int : 𝓢.y_proj x ∉ interior (𝓢.K : Set Y) := fun h_in =>
      h_x_notC ⟨h_in, h_tau_x_pos⟩
    have h_x_in_Kf : x ∈ 𝓢.K_f_lifted := h_yp_x_in_K
    have h_x_not_int_Kf : x ∉ interior 𝓢.K_f_lifted := by
      rw [𝓢.interior_K_f_lifted]; exact h_yp_x_not_int
    have h_x_frontier_Kf : x ∈ frontier 𝓢.K_f_lifted :=
      ⟨subset_closure h_x_in_Kf, h_x_not_int_Kf⟩
    have h_Kf_int_conv : Convex ℝ (interior 𝓢.K_f_lifted) := by
      rw [𝓢.interior_K_f_lifted]
      exact (𝓢.K.convex.interior).linear_preimage
        (IrnSetup.y_proj_linear : H X Y →L[ℝ] Y).toLinearMap
    have h_Kf_int_nonempty : (interior 𝓢.K_f_lifted).Nonempty := by
      obtain ⟨u₀, hu₀⟩ := 𝓢.C_interior_nonempty
      exact ⟨u₀, 𝓢.C_interior_subset_f_lhscb_interior hu₀⟩
    have h_grad_atTop : Filter.Tendsto (fun u => ‖𝓢.f_lhscb.grad u‖)
        (nhdsWithin x (interior 𝓢.K_f_lifted)) Filter.atTop :=
      𝓢.f_lhscb.grad_norm_tendsto_atTop h_Kf_int_conv h_Kf_int_nonempty x
        h_x_frontier_Kf
    have h_grad_atTop_C : Filter.Tendsto (fun u => ‖𝓢.f_lhscb.grad u‖)
        (nhdsWithin x 𝓢.C_interior) Filter.atTop :=
      h_grad_atTop.mono_left
        (nhdsWithin_mono x 𝓢.C_interior_subset_f_lhscb_interior)
    have h_mu_grad : Filter.Tendsto (fun u => μ * ‖𝓢.f_lhscb.grad u‖)
        (nhdsWithin x 𝓢.C_interior) Filter.atTop :=
      h_grad_atTop_C.const_mul_atTop hμ
    -- `R u := Q u + μ•u - (μ/τ_u)•e_τ` so that `T_μ u = R u + μ•f_lhscb.grad u`.
    set R : H X Y → H X Y := fun u =>
      𝓢.Q u + μ • u - (μ / 𝓢.tau_proj u) • 𝓢.e_τ with hR_def
    have h_T_eq : ∀ u : H X Y, 𝓢.T μ u = R u + μ • 𝓢.f_lhscb.grad u := by
      intro u
      show 𝓢.Q u + μ • u + μ • 𝓢.φ u =
          (𝓢.Q u + μ • u - (μ / 𝓢.tau_proj u) • 𝓢.e_τ) + μ • 𝓢.f_lhscb.grad u
      show 𝓢.Q u + μ • u +
            μ • (𝓢.f_lhscb.grad u + (-1 / 𝓢.tau_proj u) • 𝓢.e_τ) = _
      rw [smul_add, smul_smul]
      have h_arith : μ * (-1 / 𝓢.tau_proj u) = -(μ / 𝓢.tau_proj u) := by ring
      rw [h_arith, neg_smul]
      abel
    -- `R` is continuous at `x`.
    have h_R_cont : ContinuousAt R x := by
      refine ContinuousAt.sub ?_ ?_
      · refine ContinuousAt.add ?_ ?_
        · show ContinuousAt
              (fun u => 𝓢.M_apply u -
                (𝓢.Px_bilinform (𝓢.x_proj u) (𝓢.x_proj u) / 𝓢.tau_proj u) •
                  𝓢.e_τ) x
          refine ContinuousAt.sub 𝓢.M_clm.continuous.continuousAt ?_
          refine ContinuousAt.smul ?_ continuousAt_const
          refine ContinuousAt.div ?_ 𝓢.tau_proj_continuous.continuousAt
            (ne_of_gt h_tau_x_pos)
          show ContinuousAt
              (fun u => inner ℝ (𝓢.x_proj u) (𝓢.P (𝓢.x_proj u))) x
          have h_xproj : Continuous 𝓢.x_proj := by
            show Continuous fun u : H X Y => u.fst; fun_prop
          exact (Continuous.inner h_xproj
            (𝓢.P.continuous.comp h_xproj)).continuousAt
        · exact continuousAt_const.smul continuousAt_id
      · refine ContinuousAt.smul ?_ continuousAt_const
        exact ContinuousAt.div continuousAt_const
          𝓢.tau_proj_continuous.continuousAt (ne_of_gt h_tau_x_pos)
    have h_R_norm_tendsto : Filter.Tendsto (fun u => ‖R u‖)
        (nhdsWithin x 𝓢.C_interior) (nhds ‖R x‖) :=
      h_R_cont.norm.tendsto.mono_left nhdsWithin_le_nhds
    -- Lower bound: `μ ‖f_lhscb.grad u‖ - ‖R u‖ ≤ ‖T_μ u‖`.
    have h_eventually_le : ∀ᶠ u in nhdsWithin x 𝓢.C_interior,
        μ * ‖𝓢.f_lhscb.grad u‖ - ‖R u‖ ≤ ‖𝓢.T μ u‖ := by
      filter_upwards with u
      have h_grad_eq : μ • 𝓢.f_lhscb.grad u = 𝓢.T μ u - R u := by
        rw [h_T_eq u]; abel
      have h_le : ‖μ • 𝓢.f_lhscb.grad u‖ ≤ ‖𝓢.T μ u‖ + ‖R u‖ := by
        rw [h_grad_eq]; exact norm_sub_le _ _
      have h_norm_smul : ‖μ • 𝓢.f_lhscb.grad u‖ = μ * ‖𝓢.f_lhscb.grad u‖ := by
        rw [norm_smul, Real.norm_of_nonneg hμ.le]
      linarith [h_le, h_norm_smul]
    -- `μ ‖f_lhscb.grad u‖ - ‖R u‖ → +∞`.
    have h_diff_atTop : Filter.Tendsto
        (fun u => μ * ‖𝓢.f_lhscb.grad u‖ - ‖R u‖)
        (nhdsWithin x 𝓢.C_interior) Filter.atTop := by
      have h_neg : Filter.Tendsto (fun u => -‖R u‖)
          (nhdsWithin x 𝓢.C_interior) (nhds (-‖R x‖)) := h_R_norm_tendsto.neg
      have h_sum := h_mu_grad.atTop_add h_neg
      refine h_sum.congr ?_; intro u; ring
    exact Filter.tendsto_atTop_mono' _ h_eventually_le h_diff_atTop

/-- **Theorem 5 (Existence and uniqueness).** For every `μ > 0` there
is a unique central-path point. Existence by Minty's theorem applied to
`T_μ` (strictly monotone, continuous, boundary-coercive on the open
convex `C_interior`); uniqueness from strict monotonicity. -/
theorem exists_unique_centralPath (μ : ℝ) (hμ : 0 < μ) :
    ∃! u : H X Y, 𝓢.IsCentralPathPoint μ u := by
  obtain ⟨u, ⟨hu_C, hu_T⟩, _⟩ :=
    exists_unique_zero_of_strict_monotone_continuous_coercive
      𝓢.C_interior_isOpen 𝓢.C_interior_convex 𝓢.C_interior_nonempty
      (𝓢.T_continuousOn μ) (𝓢.T_strictMonotoneOn μ hμ) (𝓢.T_coercive μ hμ)
  exact ⟨u, ⟨hu_C, hu_T⟩, fun y hy => 𝓢.unique_centralPath μ hμ hy ⟨hu_C, hu_T⟩⟩

/-- The (well-defined, for `μ > 0`) central-path point at level `μ`. -/
noncomputable def centralPathPoint (μ : ℝ) (hμ : 0 < μ) : H X Y :=
  Classical.choose (𝓢.exists_unique_centralPath μ hμ).exists

theorem centralPathPoint_isCentralPathPoint (μ : ℝ) (hμ : 0 < μ) :
    𝓢.IsCentralPathPoint μ (𝓢.centralPathPoint μ hμ) :=
  Classical.choose_spec (𝓢.exists_unique_centralPath μ hμ).exists

/-- **Theorem 6 (Smoothness).** `μ ↦ u*(μ)` is `Cᵈ` on `ℝ₊₊` for any
`d ≤ deg(f) - 1`. We state this here only for `d = 2`. -/
theorem centralPathPoint_contDiff :
    ContDiffOn ℝ 2
      (fun μ : ℝ => 𝓢.centralPathPoint μ (sorry))
      (Set.Ioi 0) := sorry

end IrnSetup

end Irn
