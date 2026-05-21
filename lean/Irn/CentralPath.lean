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

/-- **Uniqueness of the central-path point.** Two central-path points
at the same `μ > 0` are equal. Strict monotonicity of `T_μ` follows
from `Q_monotone + φ_monotone + μ ⟨u-v, u-v⟩ ≥ μ ‖u-v‖² > 0` for u≠v. -/
theorem unique_centralPath (μ : ℝ) (hμ : 0 < μ)
    {u v : H X Y} (hu : 𝓢.IsCentralPathPoint μ u)
    (hv : 𝓢.IsCentralPathPoint μ v) : u = v := by
  obtain ⟨hC_u, hT_u⟩ := hu
  obtain ⟨hC_v, hT_v⟩ := hv
  -- T_μ u - T_μ v = 0 - 0 = 0, so ⟨u-v, T_μ u - T_μ v⟩ = 0.
  have h_T_diff : 𝓢.T μ u - 𝓢.T μ v = 0 := by rw [hT_u, hT_v]; abel
  have h_inner : inner ℝ (u - v) (𝓢.T μ u - 𝓢.T μ v) = 0 := by
    rw [h_T_diff, inner_zero_right]
  -- Expand T_μ u - T_μ v = (Q u - Q v) + μ•(u-v) + μ•(φ u - φ v).
  have h_expand : 𝓢.T μ u - 𝓢.T μ v =
      (𝓢.Q u - 𝓢.Q v) + μ • (u - v) + μ • (𝓢.φ u - 𝓢.φ v) := by
    unfold T; rw [smul_sub, smul_sub]; abel
  rw [h_expand] at h_inner
  rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
      real_inner_self_eq_norm_sq] at h_inner
  -- The three nonneg terms sum to 0 ⇒ each is 0, in particular μ ‖u-v‖² = 0.
  have h_Q := 𝓢.Q_monotone u (𝓢.C_interior_subset_Cplus hC_u) v
    (𝓢.C_interior_subset_Cplus hC_v)
  have h_phi := 𝓢.phi_monotone u hC_u v hC_v
  have h_norm_sq_nn : 0 ≤ ‖u - v‖ ^ 2 := sq_nonneg _
  have h_norm_sq_zero : ‖u - v‖ ^ 2 = 0 := by nlinarith
  have h_norm_zero : ‖u - v‖ = 0 := by
    have := sq_eq_zero_iff.mp h_norm_sq_zero
    exact this
  exact sub_eq_zero.mp (norm_eq_zero.mp h_norm_zero)

/-- **Theorem 5 (Existence and uniqueness).** For every `μ > 0` there
is a unique central-path point.

Uniqueness is proved (see `unique_centralPath`). Existence is sorried —
the standard proof uses topological/monotone-operator existence: `T_μ`
is continuous on `C_interior`, strictly monotone (by `Q_monotone` +
`phi_monotone` + the `μ • id` term), and coercive at the boundary (via
the LHSCB barrier). By a Minty/Brouwer-style argument, `T_μ` has a
zero in `C_interior`. -/
theorem exists_unique_centralPath (μ : ℝ) (hμ : 0 < μ) :
    ∃! u : H X Y, 𝓢.IsCentralPathPoint μ u := by
  have h_exists : ∃ u : H X Y, 𝓢.IsCentralPathPoint μ u := sorry
  obtain ⟨u, hu⟩ := h_exists
  exact ⟨u, hu, fun y hy => 𝓢.unique_centralPath μ hμ hy hu⟩

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
