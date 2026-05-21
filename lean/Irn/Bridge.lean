/-
# Bridge from `ProblemData` to `IrnSetup`

Assembles a full `IrnSetup` on `H = X × Y × ℝ` directly from a
`ProblemData`. The structural fields (`C`, `Cplus`, `ν`, `Q`, `φ`,
`e_τ`, `tau_proj`, `f_lhscb`, `M`, `Px_bilinform`, etc.) come from
`ProblemData`'s derivations, while the analytic ingredients (the
`W(u)⁻¹` dual norm, the Hessian preconditioner, the Riemannian
Josephy–Newton corrector and Lagrange multiplier, Minty's resolvent
existence, and the two Newton–Kantorovich basins) come from
`Irn.Analytic` as `sorry`-stubbed `def`s / `theorem`s on `ProblemData`.

The previous design carried the analytic ingredients in a separate
`IrnAnalytic 𝓟` hypothesis bundle; this version makes the bridge
total at the cost of routing every analytic claim through a `sorry`
in `Irn.Analytic`. Once an analytic claim is filled in there, it
propagates here automatically.

`IrnSetup.C` is mapped to `𝓟.C_interior` (the open interior of the
closed cone), since the IRN analysis lives on the interior where the
barrier is finite.
-/

import Irn.ProblemData
import Irn.Analytic
import Irn.Setting

namespace Irn
namespace ProblemData

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- **Bridge to `IrnSetup`.** Given a `ProblemData 𝓟`, assemble a full
`IrnSetup` on `H = X × Y × ℝ` (with `L²` inner product). Structural
fields are filled from `𝓟`'s derivations; analytic fields are routed
through the `sorry`-stubbed declarations in `Irn.Analytic`.

`IrnSetup.C` is set to `𝓟.C_interior` (the open interior, where the
barrier is finite), so `C_subset_Cplus`, `C_subset_f_domain`, etc., all
go through. -/
noncomputable def toIrnSetup (𝓟 : ProblemData X Y) :
    IrnSetup (ProblemData.H X Y) where
  C := 𝓟.C_interior
  Cplus := 𝓟.Cplus
  C_subset_Cplus := 𝓟.C_interior_subset_Cplus
  ν := 𝓟.ν
  ν_pos := 𝓟.ν_pos
  Q := 𝓟.Q
  φ := 𝓟.φ
  normWinv := 𝓟.normWinv
  normWinv_nonneg := 𝓟.normWinv_nonneg
  normWinv_le_norm := 𝓟.normWinv_le_norm
  normWinv_triangle := 𝓟.normWinv_triangle
  normWinv_smul := 𝓟.normWinv_smul
  M := 𝓟.M_clm
  e_τ := 𝓟.e_τ
  tau_proj := 𝓟.tau_proj
  tau_proj_pos := fun _ hu => 𝓟.tau_proj_pos hu
  inner_u_e_tau := 𝓟.inner_u_e_tau
  f_lhscb := 𝓟.f_lhscb
  C_subset_f_domain := 𝓟.C_interior_subset_f_lhscb_domain
  phi_eq_grad := fun _ _ => rfl
  normWinv_phi_bound := 𝓟.normWinv_phi_bound
  hessian_h := 𝓟.hessian_h
  rjnStep := 𝓟.rjnStep
  rjnLambda := 𝓟.rjnLambda
  tau_proj_linear := ProblemData.tau_proj_linear
  tau_proj_linear_eq := fun u => 𝓟.tau_proj_linear_apply u
  Px_bilinform := 𝓟.Px_bilinform_clm
  Px_symm := by
    intros u v
    rw [𝓟.Px_bilinform_clm_apply, 𝓟.Px_bilinform_clm_apply]
    exact 𝓟.Px_bilinform_symm _ _
  inner_u_M := by
    intros u
    rw [𝓟.M_clm_apply, 𝓟.inner_u_M, ← 𝓟.Px_bilinform_clm_apply]
  Q_eq := by
    intros _ _
    rfl
  Px_quad_form_psd := by
    intros u v
    rw [𝓟.Px_bilinform_clm_apply, 𝓟.Px_bilinform_clm_apply,
        𝓟.Px_bilinform_clm_apply]
    exact 𝓟.Px_quad_form_psd _ _ _ _
  hessian_plus_M := 𝓟.hessian_plus_M
  hessian_plus_M_eq := 𝓟.hessian_plus_M_eq
  Cplus_of_tau_proj_pos := fun _ h => 𝓟.Cplus_of_tau_proj_pos h
  rjnLambda_at_central := 𝓟.rjnLambda_at_central
  rjnLambda_continuousAt_central := 𝓟.rjnLambda_continuousAt_central
  rjnStep_norm_sq := 𝓟.rjnStep_norm_sq
  rjnStep_in_C := 𝓟.rjnStep_in_C
  resolvent_exists := 𝓟.resolvent_exists
  rjnStep_delta_contraction := 𝓟.rjnStep_delta_contraction
  rjnStep_euclidean_basin := 𝓟.rjnStep_euclidean_basin

end ProblemData
end Irn
