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

/-- `T_μ` is continuous on `C_interior`. Used by `exists_unique_centralPath`
via Minty. Sorried — composition of continuous pieces (Q has 1/τ, but
`τ > 0` on `C_interior`; φ has `f.grad` continuous from `contDiff` plus
the `(-1/τ) • e_τ` term again continuous on `C_interior`). -/
theorem T_continuousOn (μ : ℝ) : ContinuousOn (𝓢.T μ) 𝓢.C_interior := sorry

/-- `T_μ` is boundary-coercive on `C_interior` for `μ > 0`. Used by
`exists_unique_centralPath` via Minty. Sorried — comes from `f_lhscb.barrier`
and `g_lhscb.barrier` (both already proven): `φ(u) → ∞` as `u` approaches
the frontier, and the `Q + μ•id` part stays bounded near a fixed frontier
point, so `‖T_μ(u)‖ → ∞`. -/
theorem T_coercive (μ : ℝ) (hμ : 0 < μ) :
    ∀ x ∈ frontier 𝓢.C_interior,
      Filter.Tendsto (fun u => ‖𝓢.T μ u‖) (nhdsWithin x 𝓢.C_interior)
        Filter.atTop := sorry

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

/-- `C_interior` is open and non-empty (assuming the latter as a setup
prerequisite — sorried, since non-emptiness depends on the specific
`fBarrier` and `K`). -/
theorem C_interior_nonempty : 𝓢.C_interior.Nonempty := sorry

/-- `C_interior` is open. -/
theorem C_interior_isOpen : IsOpen 𝓢.C_interior := by
  show IsOpen {u : H X Y | 𝓢.y_proj u ∈ interior (𝓢.K : Set Y) ∧
                            0 < 𝓢.tau_proj u}
  have h1 : IsOpen {u : H X Y | 𝓢.y_proj u ∈ interior (𝓢.K : Set Y)} :=
    isOpen_interior.preimage 𝓢.y_proj_continuous
  have h2 : IsOpen {u : H X Y | 0 < 𝓢.tau_proj u} :=
    isOpen_Ioi.preimage 𝓢.tau_proj_continuous
  exact h1.inter h2

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
