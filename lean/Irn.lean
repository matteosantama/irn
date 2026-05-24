/-
Interior Riemannian Newton: Lean formalization.

This is the root module. It re-exports every submodule so that
`import Irn` brings every definition and theorem statement into scope.

The submodules track the structure of `paper/main.tex`:

* `Irn.Barriers`       — paper §2.1     (LHSCB, `φ`, `F*`, `G*`)
* `Irn.TrilinForm`     — polarization of a symmetric `k`-linear form
                                          by a PSD bilinear form
* `Irn.Dikin`          — paper §6.3 Lemma 16(i) (Dikin-ball Hessian
                                          Lipschitz bound + scaffold)
* `Irn.Setting`        — paper §1, §2.1 (problem data `(P, A, b, c, K, f)`,
                                          embedding, `Q`, `M`, `φ`)
* `Irn.Monotone`       — monotone operator API and a strongly-monotone
                                          C¹ existence theorem
* `Irn.CentralPath`    — paper §2.2–§3.2 (`T_μ`, existence, smoothness)
* `Irn.Analytic`       — Hessian preconditioner, `W⁻¹` dual norm,
                                          closed-form inverse existence
* `Irn.Sphere`         — paper §3.1–§3.3, §5.3 (sphere, tangency, error
                                          bound, geodesic exp_u)
* `Irn.Resolvent`      — paper §4        (closed-form inverse of H + Ψ)
* `Irn.RJN`            — paper §5        (Riemannian semi-Newton step)
* `Irn.PathFollowing`  — paper §6        (path-following complexity)
-/

import Irn.Barriers
import Irn.TrilinForm
import Irn.Dikin
import Irn.Setting
import Irn.Monotone
import Irn.CentralPath
import Irn.Analytic
import Irn.Sphere
import Irn.Resolvent
import Irn.RJN
import Irn.PathFollowing
