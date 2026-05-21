/-
# Bridge from `ProblemData` to `IrnSetup`

Packages the analytic ingredients of an `IrnSetup` that are NOT derivable
from `ProblemData` alone (Newton–Kantorovich basins, Minty's resolvent
existence, Hessian-preconditioner machinery, the `W(u)⁻¹` dual norm, and
the continuous-linear-map forms of `M`, `Px_bilinform`, and `tau_proj`)
into a single `IrnAnalytic 𝓟` structure, and assembles an `IrnSetup`
from a `ProblemData` plus that bundle.

The structural fields (`C`, `Cplus`, `ν`, `Q`, `φ`, `e_τ`, `tau_proj`,
`f_lhscb`, `inner_u_M`, `Q_eq`, `Px_quad_form_psd`, `Px_symm`,
`inner_u_e_tau`, etc.) come from `ProblemData`; the remaining analytic
fields come from `IrnAnalytic`.

`IrnSetup.C` is mapped to `𝓟.C_interior` (the open interior of the
closed cone `𝓟.C`), since the IrnSetup analysis lives on the interior
where the barrier is finite.
-/

import Irn.ProblemData
import Irn.Setting

namespace Irn

open scoped InnerProductSpace

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- The analytic ingredients of an `IrnSetup` that are not derivable
from `ProblemData` alone. Carries:

* the CLM packagings of `M`, `Px_bilinform`, and `tau_proj`, together
  with bridge equations to the `ProblemData` function versions;
* the `W(u)⁻¹` dual norm `normWinv` with its algebraic properties and
  LHSCB gradient bound;
* the Hessian preconditioner `hessian_h`, the equivalence `hessian_h + M`;
* the Riemannian Josephy–Newton corrector `rjnStep` and Lagrange
  multiplier `rjnLambda`, with their invariance, smooth-branch, and
  Newton–Kantorovich contraction properties;
* Minty's resolvent-existence statement. -/
structure IrnAnalytic (𝓟 : ProblemData X Y) where
  -- CLM packaging of structural operators:
  /-- `M` as a continuous linear map (bundles the function `𝓟.M_apply`). -/
  M_clm : ProblemData.H X Y →L[ℝ] ProblemData.H X Y
  M_clm_eq : ∀ u, M_clm u = 𝓟.M_apply u
  /-- `tau_proj` as a continuous linear functional. -/
  tau_proj_linear : ProblemData.H X Y →L[ℝ] ℝ
  tau_proj_linear_eq : ∀ u, tau_proj_linear u = 𝓟.tau_proj u
  /-- The primal bilinear form on `H` as a continuous bilinear map. -/
  Px_bilinform_clm : ProblemData.H X Y →L[ℝ] ProblemData.H X Y →L[ℝ] ℝ
  Px_bilinform_clm_eq : ∀ u v, Px_bilinform_clm u v =
    𝓟.Px_bilinform (𝓟.x_proj u) (𝓟.x_proj v)
  -- `W(u)⁻¹` dual norm machinery:
  normWinv : ProblemData.H X Y → ProblemData.H X Y → ℝ
  normWinv_nonneg : ∀ u v, 0 ≤ normWinv u v
  normWinv_le_norm : ∀ u v, normWinv u v ≤ ‖v‖
  normWinv_triangle : ∀ u v w,
    normWinv u (v + w) ≤ normWinv u v + normWinv u w
  normWinv_smul : ∀ u (r : ℝ) v, normWinv u (r • v) = |r| * normWinv u v
  normWinv_phi_bound : ∀ u ∈ 𝓟.C_interior,
    normWinv u (𝓟.φ u) ≤ Real.sqrt ((𝓟.ν : ℝ) + 1)
  -- Hessian preconditioner:
  hessian_h : ℝ → ProblemData.H X Y →
    ProblemData.H X Y →L[ℝ] ProblemData.H X Y
  hessian_plus_M : ℝ → ProblemData.H X Y →
    (ProblemData.H X Y ≃L[ℝ] ProblemData.H X Y)
  hessian_plus_M_eq : ∀ μ u v,
    (hessian_plus_M μ u : ProblemData.H X Y →L[ℝ] ProblemData.H X Y) v =
      hessian_h μ u v + M_clm v
  -- Riemannian Josephy–Newton corrector + multiplier:
  rjnStep : ℝ → ProblemData.H X Y → ProblemData.H X Y
  rjnLambda : ℝ → ProblemData.H X Y → ℝ
  rjnLambda_at_central : ∀ μ : ℝ, ∀ u : ProblemData.H X Y, 0 < μ →
    u ∈ 𝓟.C_interior →
    𝓟.Q u + μ • u + μ • 𝓟.φ u = 0 → rjnLambda μ u = 0
  rjnLambda_continuousAt_central : ∀ μ : ℝ, ∀ u : ProblemData.H X Y, 0 < μ →
    u ∈ 𝓟.C_interior →
    𝓟.Q u + μ • u + μ • 𝓟.φ u = 0 → ContinuousAt (rjnLambda μ) u
  rjnStep_norm_sq : ∀ μ : ℝ, ∀ u : ProblemData.H X Y, 0 < μ →
    ‖u‖ ^ 2 = (𝓟.ν : ℝ) + 1 → u ∈ 𝓟.C_interior →
    ‖rjnStep μ u‖ ^ 2 = (𝓟.ν : ℝ) + 1
  rjnStep_in_C : ∀ μ : ℝ, ∀ u : ProblemData.H X Y, 0 < μ →
    ‖u‖ ^ 2 = (𝓟.ν : ℝ) + 1 → u ∈ 𝓟.C_interior →
    rjnStep μ u ∈ 𝓟.C_interior
  -- Minty resolvent existence:
  resolvent_exists : ∀ μ : ℝ, ∀ u_k z : ProblemData.H X Y, 0 < μ →
    ∃ u : ProblemData.H X Y, u ∈ 𝓟.Cplus ∧ ∃ θ : ℝ, 0 < θ ∧
      (hessian_h μ u_k + M_clm) u = hessian_h μ u_k z + θ • 𝓟.e_τ ∧
      θ * 𝓟.tau_proj u = Px_bilinform_clm u u + μ
  -- Newton–Kantorovich:
  rjnStep_delta_contraction : ∃ ρ_star K_star : ℝ,
    0 < ρ_star ∧ ρ_star < 1 ∧ 1 ≤ K_star ∧
    ∀ μ : ℝ, 0 < μ → ∀ u : ProblemData.H X Y,
      ‖u‖ ^ 2 = (𝓟.ν : ℝ) + 1 → u ∈ 𝓟.C_interior →
      normWinv u (𝓟.Q u + μ • u + μ • 𝓟.φ u) / μ ≤ ρ_star →
      normWinv (rjnStep μ u)
          (𝓟.Q (rjnStep μ u) + μ • (rjnStep μ u) + μ • 𝓟.φ (rjnStep μ u)) / μ ≤
        K_star *
          (normWinv u (𝓟.Q u + μ • u + μ • 𝓟.φ u) / μ) ^ 2
  rjnStep_euclidean_basin : ∀ μ : ℝ, 0 < μ → ∀ u_star : ProblemData.H X Y,
    u_star ∈ 𝓟.C_interior → 𝓟.Q u_star + μ • u_star + μ • 𝓟.φ u_star = 0 →
    ∃ U : Set (ProblemData.H X Y), IsOpen U ∧ u_star ∈ U ∧
      ∃ K : ℝ, 0 < K ∧
      (∀ u ∈ U, ‖u‖ ^ 2 = (𝓟.ν : ℝ) + 1 → u ∈ 𝓟.C_interior →
         rjnStep μ u ∈ U) ∧
      (∀ u ∈ U, ‖u‖ ^ 2 = (𝓟.ν : ℝ) + 1 → u ∈ 𝓟.C_interior →
         ‖rjnStep μ u - u_star‖ ≤ K * ‖u - u_star‖ ^ 2)

namespace ProblemData

/-- **Bridge to `IrnSetup`.** Given a `ProblemData 𝓟` and the analytic
ingredients `𝓐 : IrnAnalytic 𝓟`, assemble a full `IrnSetup` on
`H = X × Y × ℝ` (with `L²` inner product). The structural fields are
filled from `𝓟`; the analytic fields are routed from `𝓐`.

`IrnSetup.C` is set to `𝓟.C_interior` (the open interior where the
barrier is finite), so `C_subset_Cplus`, `C_subset_f_domain`, etc., all
go through. -/
noncomputable def toIrnSetup (𝓟 : ProblemData X Y) (𝓐 : IrnAnalytic 𝓟) :
    IrnSetup (ProblemData.H X Y) where
  C := 𝓟.C_interior
  Cplus := 𝓟.Cplus
  C_subset_Cplus := 𝓟.C_interior_subset_Cplus
  ν := 𝓟.ν
  ν_pos := 𝓟.ν_pos
  Q := 𝓟.Q
  φ := 𝓟.φ
  normWinv := 𝓐.normWinv
  normWinv_nonneg := 𝓐.normWinv_nonneg
  normWinv_le_norm := 𝓐.normWinv_le_norm
  normWinv_triangle := 𝓐.normWinv_triangle
  normWinv_smul := 𝓐.normWinv_smul
  M := 𝓐.M_clm
  e_τ := 𝓟.e_τ
  tau_proj := 𝓟.tau_proj
  tau_proj_pos := fun _ hu => 𝓟.tau_proj_pos hu
  inner_u_e_tau := 𝓟.inner_u_e_tau
  f_lhscb := 𝓟.f_lhscb
  C_subset_f_domain := 𝓟.C_interior_subset_f_lhscb_domain
  phi_eq_grad := fun _ _ => rfl
  normWinv_phi_bound := 𝓐.normWinv_phi_bound
  hessian_h := 𝓐.hessian_h
  rjnStep := 𝓐.rjnStep
  rjnLambda := 𝓐.rjnLambda
  tau_proj_linear := 𝓐.tau_proj_linear
  tau_proj_linear_eq := 𝓐.tau_proj_linear_eq
  Px_bilinform := 𝓐.Px_bilinform_clm
  Px_symm := by
    intros u v
    rw [𝓐.Px_bilinform_clm_eq, 𝓐.Px_bilinform_clm_eq]
    exact 𝓟.Px_bilinform_symm _ _
  inner_u_M := by
    intros u
    rw [𝓐.M_clm_eq, 𝓟.inner_u_M, 𝓐.Px_bilinform_clm_eq]
  Q_eq := by
    intros u _hu
    show 𝓟.Q u = 𝓐.M_clm u -
      (𝓐.Px_bilinform_clm u u / 𝓟.tau_proj u) • 𝓟.e_τ
    rw [𝓐.M_clm_eq u, 𝓐.Px_bilinform_clm_eq u u]
    rfl
  Px_quad_form_psd := by
    intros u v
    rw [𝓐.Px_bilinform_clm_eq u u, 𝓐.Px_bilinform_clm_eq u v,
        𝓐.Px_bilinform_clm_eq v v]
    exact 𝓟.Px_quad_form_psd _ _ _ _
  hessian_plus_M := 𝓐.hessian_plus_M
  hessian_plus_M_eq := 𝓐.hessian_plus_M_eq
  Cplus_of_tau_proj_pos := fun _ h => 𝓟.Cplus_of_tau_proj_pos h
  rjnLambda_at_central := 𝓐.rjnLambda_at_central
  rjnLambda_continuousAt_central := 𝓐.rjnLambda_continuousAt_central
  rjnStep_norm_sq := 𝓐.rjnStep_norm_sq
  rjnStep_in_C := 𝓐.rjnStep_in_C
  resolvent_exists := 𝓐.resolvent_exists
  rjnStep_delta_contraction := 𝓐.rjnStep_delta_contraction
  rjnStep_euclidean_basin := 𝓐.rjnStep_euclidean_basin

end ProblemData

end Irn
