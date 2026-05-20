/-
Interior Riemannian Newton: Lean formalization.

This is the root module. It re-exports every submodule so that
`import Irn` brings every definition and theorem statement into scope.

The submodules track the structure of `paper/standalone.tex`:

* `Irn.Setting`        — paper §1–§2.1 (homogeneous embedding, `Q`, `M`)
* `Irn.Barriers`       — paper §2.1     (LHSCB, `φ`, `F*`, `G*`)
* `Irn.CentralPath`    — paper §2.2–§3.2 (`T_μ`, existence, smoothness)
* `Irn.Sphere`         — paper §3.1–§3.3 (sphere, tangency, error bound)
* `Irn.Resolvent`      — paper §4        (closed-form resolvent)
* `Irn.RJN`            — paper §5        (Riemannian Josephy–Newton)
* `Irn.PathFollowing`  — paper §6        (path-following complexity)

All proofs are currently `sorry`; this stage formalizes statements only.
-/

import Irn.Setting
import Irn.Barriers
import Irn.CentralPath
import Irn.Sphere
import Irn.Resolvent
import Irn.RJN
import Irn.PathFollowing
