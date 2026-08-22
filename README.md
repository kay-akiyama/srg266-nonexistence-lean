# There is no strongly regular graph with parameters (266, 45, 0, 9)

[![verify](https://github.com/kay-akiyama/srg266-nonexistence-lean/actions/workflows/verify.yml/badge.svg)](https://github.com/kay-akiyama/srg266-nonexistence-lean/actions/workflows/verify.yml)
[![licence](https://img.shields.io/badge/licence-Apache--2.0-blue.svg)](LICENSE)

A machine-checked Lean 4 and Mathlib proof that no finite simple graph is
strongly regular with parameters `(266, 45, 0, 9)`.

```lean
theorem SRG266.srg266_nonexistence {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ¬ SRG266.IsHypothetical G
```

The proof fixes a vertex and studies its local Gram lattice. This lattice
embeds in a positive-definite odd unimodular lattice of rank 15. Splitting off
norm-one directions and classifying the norm-two root system leaves five host
cases. Three root-lattice hosts are eliminated by kernel-checked finite
certificates. The other two cases would produce a quasi-symmetric
`2-(56, 12, 9)` design with block intersections `0` and `3`.

Deleting a point from such a design gives a derived `2-(45, 9, 2)` design.
Its block graph is the triangular graph `T(11)`, so the design can be expressed
as a cherry cover of `K₁₁`. The induced residual structure yields a finite
rational feasibility problem. Exact Hall cuts and integer dual certificates,
checked by Lean, refute every rooted normal form.

The final theorem uses only Lean's classical axioms:

```text
'SRG266.srg266_nonexistence' depends on axioms: [propext, Classical.choice, Quot.sound]
```

There is no `native_decide`, `Lean.ofReduceBool`, `Float`, or `sorry` in the
theorem's import closure. Generated certificates are replayed with
`decide +kernel`.

## Layout

| Path | Contents |
| --- | --- |
| `SRG266/FractionalNearFrameMain.lean` | final theorem |
| `SRG266/Lattice/` | rank-15 lattice reduction |
| `SRG266/Hosts/` | finite host eliminations |
| `SRG266/QuasiSymmetric/` | design reduction and finite obstruction |
| `SRG266/Certificates/` | kernel-checked certificate data |
| `scripts/print_axioms.lean` | axiom report |
| `docs/Literature.md` | relation to prior mathematical results |

## Verification

```bash
lake exe cache get
lake build
lake env lean scripts/print_axioms.lean
```

The full build is large. The CI workflow builds it in shards.

## LLM involvement

This project is the result of LLM-led mathematical research and formalization.
The human contributor supplied the problem and the instruction to solve it;
LLM agents carried out the mathematical exploration, proof design, Lean
implementation, certificate construction, debugging, and documentation. The
result does not rely on trusting those agents: every formal claim is checked by
the Lean kernel.

## Licence

Apache 2.0. See [`LICENSE`](LICENSE).
