/-
# Barriers (paper §2.1)

Logarithmically homogeneous self-concordant barriers (LHSCB) and the
conjugate barrier-gradient maps `F*`, `G*`, `φ`.

This first formalisation pass records only enough structure to name
the object. A future revision should refine `LHSCB` to capture the
full Nesterov–Nemirovski definition: `C³` smoothness, logarithmic
homogeneity, and the third-derivative self-concordance bound.

Paper references:
* Definition 2 (`ν`-LHSCB)
* Eq. (2.2) (Euler identity)
* §2.1 (conjugate barriers)
-/

import Mathlib.Analysis.InnerProductSpace.Basic

namespace Irn

/-- Placeholder structure for a `ν`-LHSCB on a proper convex cone
`K ⊆ V`. Carries only the function, its domain, and the inclusion
`domain ⊆ K`. Smoothness, logarithmic homogeneity, and self-concordance
are deferred. -/
structure LHSCB (V : Type*)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (K : Set V) (ν : ℕ) where
  /-- The barrier function. -/
  f : V → ℝ
  /-- The barrier domain (intended to be the interior of `K`). -/
  domain : Set V
  domain_subset : domain ⊆ K

end Irn
