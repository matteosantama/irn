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

namespace Irn

open scoped InnerProductSpace

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  (𝓢 : IrnSetup H)

/-- The central-path map `T_μ(u) = Q(u) + μ u + μ φ(u)`. -/
noncomputable def T (μ : ℝ) (u : H) : H :=
  𝓢.Q u + μ • u + μ • 𝓢.φ u

/-- `u` is a central-path point at level `μ` if `u ∈ int C` and
`T_μ(u) = 0`. -/
def IsCentralPathPoint (μ : ℝ) (u : H) : Prop :=
  u ∈ 𝓢.C ∧ T 𝓢 μ u = 0

/-- **Proposition 3 (Sphericity).** Every central-path point lies on
the sphere of radius `r = √(ν+1)`. -/
theorem centralPath_norm_sq {μ : ℝ} (hμ : 0 < μ) {u : H}
    (h : IsCentralPathPoint 𝓢 μ u) :
    ‖u‖ ^ 2 = (𝓢.ν : ℝ) + 1 := sorry

/-- **Theorem 5 (Existence and uniqueness).** For every `μ > 0` there
is a unique central-path point. -/
theorem exists_unique_centralPath (μ : ℝ) (hμ : 0 < μ) :
    ∃! u : H, IsCentralPathPoint 𝓢 μ u := sorry

/-- The (well-defined, for `μ > 0`) central-path point at level `μ`. -/
noncomputable def centralPathPoint (μ : ℝ) (hμ : 0 < μ) : H :=
  Classical.choose (exists_unique_centralPath 𝓢 μ hμ).exists

theorem centralPathPoint_isCentralPathPoint (μ : ℝ) (hμ : 0 < μ) :
    IsCentralPathPoint 𝓢 μ (centralPathPoint 𝓢 μ hμ) := sorry

/-- **Theorem 6 (Smoothness).** `μ ↦ u*(μ)` is `Cᵈ` on `ℝ₊₊` for any
`d ≤ deg(f) - 1`. We state this here only for `d = 2`. -/
theorem centralPathPoint_contDiff :
    ContDiffOn ℝ 2
      (fun μ : ℝ => centralPathPoint 𝓢 μ (sorry))
      (Set.Ioi 0) := sorry

end Irn
