# `Irn` — Lean formalization

Statement-level Lean 4 formalization of the results in
`paper/standalone.tex` (Interior Riemannian Newton). All proofs are
currently `sorry`; this first pass formalizes only the statements.

## Layout

| File                      | Paper section | Contents                                                 |
| ------------------------- | ------------- | -------------------------------------------------------- |
| `Irn/Setting.lean`        | §1–§2.1       | `IrnSetup`, `Q`, Proposition 1 (monotonicity)            |
| `Irn/Barriers.lean`       | §2.1          | `LHSCB` interface                                        |
| `Irn/CentralPath.lean`    | §2.2–§3.2     | `T_μ`, sphericity (Prop 3), existence (Thm 5), smoothness (Thm 6) |
| `Irn/Sphere.lean`         | §3            | sphere, projector, tangentiality (Lemma 6), error bound (Thm 7) |
| `Irn/Resolvent.lean`      | §4 + App.     | resolvent (Thm 8), maximal monotone extension (Lemma A.1) |
| `Irn/RJN.lean`            | §5            | Riemannian Josephy–Newton, λ existence (Prop 11), quadratic conv (Thm 12) |
| `Irn/PathFollowing.lean`  | §6            | transfer identity, Prop 12 (Euclidean failure), Lemmas 13–15, Thm 16 |

The ambient finite-dimensional real Hilbert space `H` is abstract.
`IrnSetup H` bundles the cones, the KKT operator `Q`, the
barrier-gradient map `φ`, and the *Euler-type identities* and
monotonicity that the paper derives from the explicit block matrix
`M`. We do not carry the matrix data itself, so those identities
appear as fields of `IrnSetup` rather than as theorems with content
proofs.

## Building

The toolchain is pinned to `leanprover/lean4:v4.29.1` (matches the
locally installed Lean). The single dependency is Mathlib. From this
directory:

```sh
lake update            # fetch Mathlib
lake exe cache get     # download pre-built Mathlib oleans (~30 min savings)
lake build             # build Irn
```

If Mathlib `master` demands a different Lean version, update
`lean-toolchain` to match Mathlib's `lean-toolchain` and rerun
`lake update`.

## Known rough edges

This is a first pass; expect to refine:

* **`LHSCB`** is a placeholder — only the smoothness and Euler
  identity are recorded; the self-concordant third-derivative bound is
  not yet captured.
* **`Irn.Resolvent`** uses `sorry` placeholders for `graphPsi`,
  `resolvent`, and the full statement of Theorem 8, because the
  concrete `M`, `e_τ`, `P` data is not abstracted in this pass.
* **`Irn.RJN.IsRJNStepA / IsRJNStepB`** are `sorry`-stubs — the
  augmented Newton inclusion is named but not fleshed out.
* **`Irn.PathFollowing.W`** and **`normWinv`** are stubs; the Hessian
  metric `W(u) = I + ∇²F*(u)` requires `F*` to be more than just `φ`'s
  potential (i.e., we need `φ` exhibited as a gradient with a known
  Hessian).
* Notation and exact field types may not compile against the current
  Mathlib; this pass prioritises matching the paper over passing
  `lake build`. Tighten incrementally.
