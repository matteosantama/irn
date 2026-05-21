/-
# Central Path (paper §2.2–§3.2)

The central-path map `T_μ : Cplus → H`, the central-path point at
level `μ`, existence and uniqueness (Theorem 6), and smoothness in `μ`
(Theorem 7).

Paper references:
* §2.2 Definition 3 (central path)
* §2.3 Proposition 4 (sphericity) → `centralPath_norm_sq`
* §3.2 Theorem 6 (existence and uniqueness)
* §3.2 Theorem 7 (smoothness)
-/

import Irn.Setting
import Irn.Monotone
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ImplicitContDiff

open scoped ContDiff

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

/-- **Proposition 4 (Sphericity).** Every central-path point lies on
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

/-- `T_μ` is **strongly monotone** on `C_interior` with constant `μ`:
`μ ‖u-v‖² ≤ ⟨u-v, T_μ u - T_μ v⟩`. This is the quantitative form of
the strict monotonicity below, used by the Minty-style existence
theorem `exists_unique_zero_of_stronglyMonotone_C1_coercive`. -/
theorem T_stronglyMonotoneOn (μ : ℝ) (hμ : 0 < μ) :
    IsStronglyMonotoneOn (𝓢.T μ) 𝓢.C_interior μ := by
  intro u hu v hv
  have h_expand : 𝓢.T μ u - 𝓢.T μ v =
      (𝓢.Q u - 𝓢.Q v) + μ • (u - v) + μ • (𝓢.φ u - 𝓢.φ v) := by
    unfold T; rw [smul_sub, smul_sub]; abel
  rw [h_expand, inner_add_right, inner_add_right, inner_smul_right,
      inner_smul_right, real_inner_self_eq_norm_sq]
  have h_Q := 𝓢.Q_monotone u (𝓢.C_interior_subset_Cplus hu) v
    (𝓢.C_interior_subset_Cplus hv)
  have h_phi := 𝓢.phi_monotone u hu v hv
  have h_mu_phi : 0 ≤ μ * inner ℝ (u - v) (𝓢.φ u - 𝓢.φ v) :=
    mul_nonneg hμ.le h_phi
  linarith

/-- `T_μ` is strictly monotone on `C_interior` for `μ > 0`. Follows from
strong monotonicity (with constant `μ > 0`). -/
theorem T_strictMonotoneOn (μ : ℝ) (hμ : 0 < μ) :
    IsStrictMonotoneOn (𝓢.T μ) 𝓢.C_interior :=
  (𝓢.T_stronglyMonotoneOn μ hμ).isStrictMonotoneOn hμ

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
    have := 𝓢.f_lhscb.contDiff₃.fderivWithin
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
    (𝓢.fBarrier.contDiff₃.differentiableOn (by norm_num)).differentiableAt
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

/-! ### Smoothness helpers for `T_contDiffOn1` and `T_joint_contDiffAt`

These intermediate lemmas establish `C^(d-1)` smoothness of the
constituent pieces of `T = Q + μ•id + μ•φ` on `C_interior`. They feed
both the `C¹` regularity hypothesis of the corrected Minty existence
theorem and the joint smoothness needed by the IFT proof of
`centralPathPoint_contDiff`. -/

/-- `(𝓢.d - 1) + 1 = 𝓢.d` (in `ℕ∞ω`): the standard `tsub` identity
specialised to our setting (`d ≥ 3 ⇒ 1 ≤ d`). -/
lemma d_sub_one_add_one_eq :
    ((𝓢.d - 1 : ℕ∞) : ℕ∞ω) + 1 = ((𝓢.d : ℕ∞) : ℕ∞ω) := by
  have h1 : (1 : ℕ∞) ≤ 𝓢.d := le_trans (by decide) 𝓢.hd_ge
  have hcancel : (𝓢.d - 1) + 1 = 𝓢.d := tsub_add_cancel_of_le h1
  exact_mod_cast hcancel

/-- `f_lhscb.grad` is `C^(d-1)` on `interior K_f_lifted`. Uses
`ContDiffOn.fderivWithin` to drop one derivative from `f_lhscb.contDiff`,
then composes with the Riesz isomorphism `(toDual ℝ H).symm` which is
a continuous linear equiv (hence `C^∞`). -/
theorem f_lhscb_grad_contDiffOn :
    ContDiffOn ℝ (𝓢.d - 1) 𝓢.f_lhscb.grad (interior 𝓢.K_f_lifted) := by
  have h_fderiv_within : ContDiffOn ℝ (𝓢.d - 1)
      (fderivWithin ℝ 𝓢.f_lhscb.f (interior 𝓢.K_f_lifted))
      (interior 𝓢.K_f_lifted) := by
    refine 𝓢.f_lhscb.contDiff.fderivWithin isOpen_interior.uniqueDiffOn ?_
    have h1 : (1 : ℕ∞ω) ≤ ((𝓢.d : ℕ∞) : ℕ∞ω) := by
      have h : (1 : ℕ∞) ≤ 𝓢.d := le_trans (by decide) 𝓢.hd_ge
      exact_mod_cast h
    exact (tsub_add_cancel_of_le h1).le
  have h_fderiv : ContDiffOn ℝ (𝓢.d - 1) (fderiv ℝ 𝓢.f_lhscb.f)
      (interior 𝓢.K_f_lifted) :=
    h_fderiv_within.congr
      (fun y hy => (fderivWithin_of_isOpen isOpen_interior hy).symm)
  show ContDiffOn ℝ (𝓢.d - 1) (fun u =>
      (InnerProductSpace.toDual ℝ (H X Y)).symm (fderiv ℝ 𝓢.f_lhscb.f u))
      (interior 𝓢.K_f_lifted)
  have h_clm : ContDiff ℝ (𝓢.d - 1)
      (InnerProductSpace.toDual ℝ (H X Y)).symm.toContinuousLinearEquiv :=
    ContinuousLinearEquiv.contDiff _
  exact h_clm.comp_contDiffOn h_fderiv

theorem f_lhscb_grad_contDiffAt {u₀ : H X Y}
    (hu₀ : u₀ ∈ interior 𝓢.K_f_lifted) :
    ContDiffAt ℝ (𝓢.d - 1) 𝓢.f_lhscb.grad u₀ :=
  (𝓢.f_lhscb_grad_contDiffOn _ hu₀).contDiffAt
    (isOpen_interior.mem_nhds hu₀)

/-- `(-1/τ_u) • e_τ` is `C^∞` at any `u` with `τ_u > 0`. -/
theorem g_grad_contDiffAt {u₀ : H X Y} (hu₀ : u₀ ∈ 𝓢.Cplus) :
    ContDiffAt ℝ (𝓢.d - 1)
      (fun u : H X Y => (-1 / 𝓢.tau_proj u) • 𝓢.e_τ) u₀ := by
  have hτ : 0 < 𝓢.tau_proj u₀ := hu₀
  have h_tau_cd : ContDiffAt ℝ (𝓢.d - 1) 𝓢.tau_proj u₀ :=
    (IrnSetup.tau_proj_linear : H X Y →L[ℝ] ℝ).contDiff.contDiffAt
  have h_inv_cd : ContDiffAt ℝ (𝓢.d - 1)
      (fun u : H X Y => -1 / 𝓢.tau_proj u) u₀ :=
    (contDiffAt_const (c := (-1 : ℝ))).div h_tau_cd (ne_of_gt hτ)
  exact h_inv_cd.smul_const 𝓢.e_τ

/-- `φ` is `C^(d-1)` at any `u₀ ∈ C_interior`. -/
theorem phi_contDiffAt {u₀ : H X Y} (hu₀ : u₀ ∈ 𝓢.C_interior) :
    ContDiffAt ℝ (𝓢.d - 1) 𝓢.φ u₀ := by
  show ContDiffAt ℝ (𝓢.d - 1)
    (fun u => 𝓢.f_lhscb.grad u + (-1 / 𝓢.tau_proj u) • 𝓢.e_τ) u₀
  exact (𝓢.f_lhscb_grad_contDiffAt
    (𝓢.C_interior_subset_f_lhscb_interior hu₀)).add (𝓢.g_grad_contDiffAt hu₀.2)

/-- `Q` is `C^(d-1)` at any `u₀ ∈ Cplus`. The proof uses
`contDiff_inner` with explicit `𝕜 := ℝ` and `E := X` to side-step a
`NormedSpace` typeclass elaboration ambiguity. -/
theorem Q_contDiffAt {u₀ : H X Y} (hu₀ : u₀ ∈ 𝓢.Cplus) :
    ContDiffAt ℝ (𝓢.d - 1) 𝓢.Q u₀ := by
  have hτ : 0 < 𝓢.tau_proj u₀ := hu₀
  show ContDiffAt ℝ (𝓢.d - 1)
    (fun u : H X Y => 𝓢.M_apply u -
      (𝓢.Px_bilinform (𝓢.x_proj u) (𝓢.x_proj u) / 𝓢.tau_proj u) • 𝓢.e_τ) u₀
  refine ContDiffAt.sub ?_ ?_
  · exact 𝓢.M_clm.contDiff.contDiffAt
  · refine ContDiffAt.smul_const ?_ 𝓢.e_τ
    have h_xp : ContDiffAt ℝ (𝓢.d - 1) 𝓢.x_proj u₀ :=
      (IrnSetup.x_proj_linear : H X Y →L[ℝ] X).contDiff.contDiffAt
    have h_tp : ContDiffAt ℝ (𝓢.d - 1) 𝓢.tau_proj u₀ :=
      (IrnSetup.tau_proj_linear : H X Y →L[ℝ] ℝ).contDiff.contDiffAt
    have h_P : ContDiffAt ℝ (𝓢.d - 1) (fun u : H X Y => 𝓢.P (𝓢.x_proj u)) u₀ :=
      (𝓢.P.contDiff.contDiffAt).comp u₀ h_xp
    have h_Pxbil : ContDiffAt ℝ (𝓢.d - 1)
        (fun u : H X Y => 𝓢.Px_bilinform (𝓢.x_proj u) (𝓢.x_proj u)) u₀ := by
      show ContDiffAt ℝ (𝓢.d - 1)
        (fun u : H X Y => inner ℝ (𝓢.x_proj u) (𝓢.P (𝓢.x_proj u))) u₀
      have h_inner_cd : ContDiff ℝ (𝓢.d - 1)
          (fun p : X × X => inner ℝ p.1 p.2) :=
        (isBoundedBilinearMap_inner (𝕜 := ℝ) (E := X)).contDiff
      exact h_inner_cd.contDiffAt.comp u₀ (h_xp.prodMk h_P)
    exact h_Pxbil.div h_tp (ne_of_gt hτ)

/-- `T_μ` is `C^(d-1)` (in particular `C¹`) on `C_interior`. The
regularity hypothesis used by the corrected Minty existence theorem
and by the IFT-based smoothness of `centralPathMap`. -/
theorem T_contDiffOn (μ : ℝ) :
    ContDiffOn ℝ (𝓢.d - 1) (𝓢.T μ) 𝓢.C_interior := by
  intro u₀ hu₀
  refine ContDiffAt.contDiffWithinAt ?_
  show ContDiffAt ℝ (𝓢.d - 1)
    (fun u : H X Y => 𝓢.Q u + μ • u + μ • 𝓢.φ u) u₀
  have h_Q : ContDiffAt ℝ (𝓢.d - 1) 𝓢.Q u₀ := 𝓢.Q_contDiffAt hu₀.2
  have h_id : ContDiffAt ℝ (𝓢.d - 1) (fun u : H X Y => u) u₀ := contDiffAt_id
  have h_phi : ContDiffAt ℝ (𝓢.d - 1) 𝓢.φ u₀ := 𝓢.phi_contDiffAt hu₀
  have h_smulId : ContDiffAt ℝ (𝓢.d - 1) (fun u : H X Y => μ • u) u₀ :=
    h_id.const_smul μ
  have h_smulPhi : ContDiffAt ℝ (𝓢.d - 1) (fun u : H X Y => μ • 𝓢.φ u) u₀ :=
    h_phi.const_smul μ
  exact (h_Q.add h_smulId).add h_smulPhi

/-- `T_μ` is `C¹` on `C_interior` (downgrade of `T_contDiffOn`). -/
theorem T_contDiffOn1 (μ : ℝ) : ContDiffOn ℝ 1 (𝓢.T μ) 𝓢.C_interior := by
  refine (𝓢.T_contDiffOn μ).of_le ?_
  have h2 : (2 : ℕ∞) ≤ 𝓢.d - 1 := by
    have h3 : (3 : ℕ∞) ≤ 𝓢.d := 𝓢.hd_ge
    have h_sub : (3 : ℕ∞) - 1 ≤ 𝓢.d - 1 := tsub_le_tsub_right h3 1
    have h_eq : (3 : ℕ∞) - 1 = 2 := by decide
    rw [h_eq] at h_sub
    exact h_sub
  have h12' : (1 : ℕ∞) ≤ 𝓢.d - 1 := le_trans (by decide) h2
  exact_mod_cast h12'

/-- **Theorem 6 (Existence and uniqueness).** For every `μ > 0` there
is a unique central-path point. Existence by the corrected Minty-style
theorem `exists_unique_zero_of_stronglyMonotone_C1_coercive` applied to
`T_μ` (continuous, strongly monotone with constant `μ`, `C¹`, boundary-
coercive on the open convex `C_interior`). -/
theorem exists_unique_centralPath (μ : ℝ) (hμ : 0 < μ) :
    ∃! u : H X Y, 𝓢.IsCentralPathPoint μ u := by
  obtain ⟨u, ⟨hu_C, hu_T⟩, _⟩ :=
    exists_unique_zero_of_stronglyMonotone_C1_coercive
      𝓢.C_interior_isOpen 𝓢.C_interior_convex 𝓢.C_interior_nonempty
      (𝓢.T_continuousOn μ) hμ
      (𝓢.T_stronglyMonotoneOn μ hμ)
      (𝓢.T_contDiffOn1 μ)
      (𝓢.T_coercive μ hμ)
  exact ⟨u, ⟨hu_C, hu_T⟩, fun y hy => 𝓢.unique_centralPath μ hμ hy ⟨hu_C, hu_T⟩⟩

/-- The (well-defined, for `μ > 0`) central-path point at level `μ`. -/
noncomputable def centralPathPoint (μ : ℝ) (hμ : 0 < μ) : H X Y :=
  Classical.choose (𝓢.exists_unique_centralPath μ hμ).exists

theorem centralPathPoint_isCentralPathPoint (μ : ℝ) (hμ : 0 < μ) :
    𝓢.IsCentralPathPoint μ (𝓢.centralPathPoint μ hμ) :=
  Classical.choose_spec (𝓢.exists_unique_centralPath μ hμ).exists

/-- The central-path map `μ ↦ u*(μ)` extended to all of `ℝ` by `0`
outside `(0, ∞)`. Convenient for stating smoothness without threading
the positivity hypothesis through the function argument. -/
noncomputable def centralPathMap (𝓢 : IrnSetup X Y) : ℝ → H X Y :=
  fun μ => if h : 0 < μ then 𝓢.centralPathPoint μ h else 0

/-- `centralPathMap` agrees with `centralPathPoint` on `Ioi 0`. -/
theorem centralPathMap_of_pos {μ : ℝ} (hμ : 0 < μ) :
    𝓢.centralPathMap μ = 𝓢.centralPathPoint μ hμ := by
  show (if h : 0 < μ then 𝓢.centralPathPoint μ h else 0) = _
  rw [dif_pos hμ]

/-! ### Smoothness of the central-path map (Theorem 7)

The proof applies Mathlib's implicit function theorem
(`ContDiffAt.contDiffAt_implicitFunction`) to `T_μ(u) = 0`:

1. `T_joint (μ, u) = T_μ u` is `C^(d-1)` jointly: `Q u + μ•u` is `C^∞`
   on `Cplus`, and `μ • φ u = μ • F_lhscb.grad u` inherits one
   derivative less than `F_lhscb` (which is `C^d`).
2. The partial derivative `D_u T_μ(u)` at `u = u*(μ)` is invertible:
   for all `v`,
   `⟨v, (D_u T_μ(u)) v⟩ = ⟨v, D_u Q(u) v⟩ + μ‖v‖² + μ ⟨v, ∇²F_lhscb(u) v⟩`.
   `D_u Q` and `∇²F_lhscb` are PSD (the former from `Q_monotone` after
   differentiation, the latter from `self_concordant_hessian_nonneg`),
   and `μ > 0`. So `D_u T_μ(u)` is positive definite — in finite
   dimensions, injective ⇒ bijective ⇒ invertible.
3. The implicit function `ψ : ℝ → H` produced by IFT satisfies
   `ψ μ₀ = u*(μ₀)` and `T_μ (ψ μ) = 0` locally. By continuity of `ψ`
   and openness of `C_interior`, `ψ μ ∈ C_interior` near `μ₀`. By
   uniqueness of the central path, `ψ μ = u*(μ) = centralPathMap μ`. -/

/-- The joint function `T_joint (μ, u) = T_μ u`. -/
noncomputable def T_joint (𝓢 : IrnSetup X Y) : ℝ × H X Y → H X Y :=
  fun p => 𝓢.T p.1 p.2

/-- **Joint smoothness of `T_joint`.** At any `(μ₀, u₀)` with `μ₀ > 0`
and `u₀ ∈ C_interior`, `T_joint` is `C^(d-1)`. The smoothness is
limited by `μ • F_lhscb.grad u` — `F_lhscb.grad` is `C^(d-1)` because
`F_lhscb.f` is `C^d` and the gradient is one derivative of `f` (via
the Riesz isomorphism, which is `C^∞`). The other pieces (`Q`,
`μ•u`) are `C^∞`.

**Sketch:** assemble from the three helpers `Q_contDiffAt`,
`phi_contDiffAt`, and bilinearity of scalar multiplication.

```
T_joint p = Q p.2 + p.1 • p.2 + p.1 • φ p.2
```

The proof composes the single-variable smoothness lemmas
(`Q_contDiffAt`, `phi_contDiffAt`) with `Prod.snd` and uses bilinearity
of scalar multiplication. -/
theorem T_joint_contDiffAt {μ₀ : ℝ} (_hμ₀ : 0 < μ₀)
    {u₀ : H X Y} (hu₀ : u₀ ∈ 𝓢.C_interior) :
    ContDiffAt ℝ (𝓢.d - 1) 𝓢.T_joint (μ₀, u₀) := by
  show ContDiffAt ℝ (𝓢.d - 1)
    (fun p : ℝ × H X Y => 𝓢.Q p.2 + p.1 • p.2 + p.1 • 𝓢.φ p.2) (μ₀, u₀)
  have h_fst : ContDiffAt ℝ (𝓢.d - 1) (Prod.fst : ℝ × H X Y → ℝ) (μ₀, u₀) :=
    contDiffAt_fst
  have h_snd : ContDiffAt ℝ (𝓢.d - 1)
      (Prod.snd : ℝ × H X Y → H X Y) (μ₀, u₀) := contDiffAt_snd
  have h_Q : ContDiffAt ℝ (𝓢.d - 1)
      (fun p : ℝ × H X Y => 𝓢.Q p.2) (μ₀, u₀) :=
    (𝓢.Q_contDiffAt hu₀.2).fun_comp (μ₀, u₀) h_snd
  have h_phi : ContDiffAt ℝ (𝓢.d - 1)
      (fun p : ℝ × H X Y => 𝓢.φ p.2) (μ₀, u₀) :=
    (𝓢.phi_contDiffAt hu₀).fun_comp (μ₀, u₀) h_snd
  have h_smulId : ContDiffAt ℝ (𝓢.d - 1)
      (fun p : ℝ × H X Y => p.1 • p.2) (μ₀, u₀) := h_fst.smul h_snd
  have h_smulPhi : ContDiffAt ℝ (𝓢.d - 1)
      (fun p : ℝ × H X Y => p.1 • 𝓢.φ p.2) (μ₀, u₀) := h_fst.smul h_phi
  exact (h_Q.add h_smulId).add h_smulPhi

/-- `𝓢.d - 1 ≠ 0` (in `ℕ∞ω`): immediate from `𝓢.d ≥ 3` since `d - 1`
in `ℕ∞` is zero only when `d ≤ 1`, contradicting `3 ≤ d`. -/
theorem d_sub_one_ne_zero : ((𝓢.d - 1 : ℕ∞) : ℕ∞ω) ≠ 0 := by
  intro heq
  have h0 : 𝓢.d - 1 = (0 : ℕ∞) := by exact_mod_cast heq
  have h_le_1 : 𝓢.d ≤ 1 := tsub_eq_zero_iff_le.mp h0
  have h_3_le_1 : (3 : ℕ∞) ≤ 1 := 𝓢.hd_ge.trans h_le_1
  exact absurd h_3_le_1 (by decide)

/-- **Invertibility of `D_u T_μ` at central-path points.** The partial
derivative of `T_joint` in the `u`-direction at `(μ, u)` (with `μ > 0`
and `u ∈ C_interior`) is positive-definite, hence invertible in finite
dimensions.

Proof:
* `T μ = T_joint ∘ (Prod.mk μ)`, and `fderiv (Prod.mk μ) u = inr`, so
  by the chain rule `fderiv (T μ) u = (fderiv T_joint (μ, u)) ∘L inr`.
* `T μ` is strongly monotone (with constant `μ`) and `C¹` on
  `C_interior`, so by `fderiv_inner_lower_bound` we have
  `μ ‖h‖² ≤ ⟨h, fderiv (T μ) u h⟩` for all `h`.
* Hence `fderiv (T μ) u` is injective; by `fderiv_range_eq_top` it is
  also surjective. So it is a `ContinuousLinearEquiv` (in finite dim),
  i.e. invertible. -/
theorem T_partial_u_isInvertible {μ : ℝ} (hμ : 0 < μ)
    {u : H X Y} (hu : u ∈ 𝓢.C_interior) :
    ((fderiv ℝ 𝓢.T_joint (μ, u)).comp
      (ContinuousLinearMap.inr ℝ ℝ (H X Y))).IsInvertible := by
  -- `T μ = T_joint ∘ (Prod.mk μ)`, so by the chain rule its `fderiv` at
  -- `u` is `(fderiv T_joint (μ, u)).comp inr`.
  set L : H X Y →L[ℝ] H X Y :=
    (fderiv ℝ 𝓢.T_joint (μ, u)).comp (ContinuousLinearMap.inr ℝ ℝ (H X Y))
    with hL_def
  have h_T_C1 : ContDiffOn ℝ 1 (𝓢.T μ) 𝓢.C_interior := 𝓢.T_contDiffOn1 μ
  have h_T_joint_diff : DifferentiableAt ℝ 𝓢.T_joint (μ, u) :=
    (𝓢.T_joint_contDiffAt hμ hu).differentiableAt 𝓢.d_sub_one_ne_zero
  have h_mk_HasFDerivAt :
      HasFDerivAt (fun u' : H X Y => ((μ, u') : ℝ × H X Y))
        (ContinuousLinearMap.inr ℝ ℝ (H X Y)) u := by
    have h_const_fd : HasFDerivAt (fun _ : H X Y => μ) (0 : H X Y →L[ℝ] ℝ) u :=
      hasFDerivAt_const μ u
    have h_id_fd : HasFDerivAt (fun u' : H X Y => u')
        (ContinuousLinearMap.id ℝ (H X Y)) u := hasFDerivAt_id u
    have h_prod := h_const_fd.prodMk h_id_fd
    convert h_prod using 1
  have h_T_joint_HasFDerivAt :
      HasFDerivAt 𝓢.T_joint (fderiv ℝ 𝓢.T_joint (μ, u)) (μ, u) :=
    h_T_joint_diff.hasFDerivAt
  have h_T_HasFDerivAt : HasFDerivAt (𝓢.T μ) L u :=
    h_T_joint_HasFDerivAt.comp u h_mk_HasFDerivAt
  have h_T_fderiv_eq : fderiv ℝ (𝓢.T μ) u = L := h_T_HasFDerivAt.fderiv
  -- Surjectivity from `fderiv_range_eq_top`.
  have h_range : (↑L : H X Y →ₗ[ℝ] H X Y).range = ⊤ := by
    rw [← h_T_fderiv_eq]
    exact fderiv_range_eq_top 𝓢.C_interior_isOpen hμ
      (𝓢.T_stronglyMonotoneOn μ hμ) h_T_C1 u hu
  -- Injectivity from `fderiv_inner_lower_bound`.
  have h_inj : (↑L : H X Y →ₗ[ℝ] H X Y).ker = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro h h_mem
    -- `h ∈ ker L`, i.e. `L h = 0`.
    have hL_h_zero : L h = 0 := h_mem
    -- From `μ ‖h‖² ≤ ⟨h, L h⟩ = 0` and `μ > 0`, deduce `h = 0`.
    have h_bound : μ * ‖h‖ ^ 2 ≤ inner ℝ h (fderiv ℝ (𝓢.T μ) u h) :=
      fderiv_inner_lower_bound 𝓢.C_interior_isOpen hμ
        (𝓢.T_stronglyMonotoneOn μ hμ) h_T_C1 u hu h
    rw [h_T_fderiv_eq, hL_h_zero, inner_zero_right] at h_bound
    have h_norm_sq_zero : ‖h‖ ^ 2 = 0 := by
      have h_nn : 0 ≤ ‖h‖ ^ 2 := sq_nonneg _
      nlinarith
    have h_norm_zero : ‖h‖ = 0 := by
      have := sq_eq_zero_iff.mp h_norm_sq_zero
      exact this
    exact norm_eq_zero.mp h_norm_zero
  -- Construct the `ContinuousLinearEquiv`.
  exact ⟨ContinuousLinearEquiv.ofBijective L h_inj h_range, rfl⟩

/-- **Theorem 7 (Smoothness).** If the user's barrier `fBarrier` has
smoothness degree `d ≥ 3` (recorded in `𝓢.d`, with `d = ⊤` denoting
`C^∞`), then the central-path map `μ ↦ u*(μ)` is `C^(d-1)` on the open
ray `(0, ∞)`. (When `d = ⊤`, `d - 1 = ⊤` so the conclusion is `C^∞`.)

Strategy: apply the implicit function theorem to `T_μ(u) = 0` at each
`μ₀ > 0`, using joint smoothness of `T` (`T_joint_contDiffAt`) and
positive-definiteness of the partial derivative `D_u T`
(`T_partial_u_isInvertible`). Identify the implicit function with
`centralPathMap` via uniqueness of central-path points. -/
theorem centralPathPoint_contDiff :
    ContDiffOn ℝ (𝓢.d - 1) 𝓢.centralPathMap (Set.Ioi 0) := by
  intro μ₀ hμ₀
  have h_C : 𝓢.centralPathPoint μ₀ hμ₀ ∈ 𝓢.C_interior :=
    (𝓢.centralPathPoint_isCentralPathPoint μ₀ hμ₀).1
  have h_cdaT := 𝓢.T_joint_contDiffAt hμ₀ h_C
  have h_inv := 𝓢.T_partial_u_isInvertible hμ₀ h_C
  -- IFT: the implicit function `ψ` of `T_joint` is `C^(d-1)` at `μ₀`.
  set ψ : ℝ → H X Y :=
    h_cdaT.implicitFunction 𝓢.d_sub_one_ne_zero h_inv with hψ_def
  have h_implicit_cd : ContDiffAt ℝ (𝓢.d - 1) ψ μ₀ :=
    h_cdaT.contDiffAt_implicitFunction 𝓢.d_sub_one_ne_zero h_inv
  -- `ψ` equals `centralPathMap` on a neighbourhood of `μ₀`:
  -- 1. `ψ μ₀ = u*(μ₀) ∈ C_interior` (apply_self), and `ψ` is continuous,
  --    so `ψ μ ∈ C_interior` for `μ` near `μ₀` (since `C_interior` is open).
  -- 2. By IFT, `T_joint (μ, ψ μ) = T_joint (μ₀, u*(μ₀)) = 0` near `μ₀`.
  -- 3. So `(ψ μ, μ)` is a central path point at `μ` (for `μ > 0` near `μ₀`),
  --    and by uniqueness `ψ μ = centralPathPoint μ = centralPathMap μ`.
  have h_eq : 𝓢.centralPathMap =ᶠ[nhds μ₀] ψ := by
    have h_ψ_self : ψ μ₀ = 𝓢.centralPathPoint μ₀ hμ₀ :=
      h_cdaT.implicitFunction_apply_self 𝓢.d_sub_one_ne_zero h_inv
    have h_ψ_cont : ContinuousAt ψ μ₀ := h_implicit_cd.continuousAt
    have h_ψ_in_C : ∀ᶠ μ in nhds μ₀, ψ μ ∈ 𝓢.C_interior := by
      have h_self_in : ψ μ₀ ∈ 𝓢.C_interior := h_ψ_self ▸ h_C
      exact h_ψ_cont (𝓢.C_interior_isOpen.mem_nhds h_self_in)
    have h_μ_pos : ∀ᶠ μ in nhds μ₀, 0 < μ :=
      isOpen_Ioi.mem_nhds hμ₀
    have h_T_base : 𝓢.T_joint (μ₀, 𝓢.centralPathPoint μ₀ hμ₀) = 0 :=
      (𝓢.centralPathPoint_isCentralPathPoint μ₀ hμ₀).2
    have h_T_apply :=
      h_cdaT.eventually_apply_implicitFunction 𝓢.d_sub_one_ne_zero h_inv
    -- `h_T_apply : ∀ᶠ μ in 𝓝 μ₀, T_joint (μ, ψ μ) = T_joint (μ₀, u*(μ₀))`.
    have h_T_zero : ∀ᶠ μ in nhds μ₀, 𝓢.T_joint (μ, ψ μ) = 0 := by
      filter_upwards [h_T_apply] with μ hμ
      rw [hμ, h_T_base]
    filter_upwards [h_ψ_in_C, h_μ_pos, h_T_zero] with μ h_ψC h_μp h_T0
    rw [𝓢.centralPathMap_of_pos h_μp]
    exact 𝓢.unique_centralPath μ h_μp
      (𝓢.centralPathPoint_isCentralPathPoint μ h_μp) ⟨h_ψC, h_T0⟩
  exact (h_implicit_cd.congr_of_eventuallyEq h_eq).contDiffWithinAt

end IrnSetup

end Irn
