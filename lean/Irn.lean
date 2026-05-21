/-
Interior Riemannian Newton: Lean formalization.

This is the root module. It re-exports every submodule so that
`import Irn` brings every definition and theorem statement into scope.

The submodules track the structure of `paper/standalone.tex`:

* `Irn.Barriers`       — paper §2.1     (LHSCB, `φ`, `F*`, `G*`)
* `Irn.Setting`    — paper §1–§2.2  (problem data `(P, A, b, c, K, f)`,
                                          embedding, `Q`, `M`, `φ`)
* `Irn.Analytic`       — sorry'd analytic content (Newton-Kantorovich,
                                          Minty, Hessian preconditioner)
* `Irn.CentralPath`    — paper §2.2–§3.2 (`T_μ`, existence, smoothness)
* `Irn.Sphere`         — paper §3.1–§3.3 (sphere, tangency, error bound)
* `Irn.Resolvent`      — paper §4        (closed-form resolvent)
* `Irn.RJN`            — paper §5        (Riemannian Josephy–Newton)
* `Irn.PathFollowing`  — paper §6        (path-following complexity)
-/

import Irn.Barriers
import Irn.Setting
import Irn.Analytic
import Irn.CentralPath
import Irn.Sphere
import Irn.Resolvent
import Irn.RJN
import Irn.PathFollowing
