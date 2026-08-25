# There is no strongly regular graph with parameters (266, 45, 0, 9)

[![verify](https://github.com/kay-akiyama/srg266-nonexistence-lean/actions/workflows/verify.yml/badge.svg)](https://github.com/kay-akiyama/srg266-nonexistence-lean/actions/workflows/verify.yml)
[![licence](https://img.shields.io/badge/licence-Apache--2.0-blue.svg)](LICENSE)

A machine-checked Lean 4 and Mathlib proof that no finite simple graph is
strongly regular with parameters `(266, 45, 0, 9)`.

```lean
theorem SRG266.srg266_nonexistence {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ¬ G.IsSRGWith 266 45 0 9
```

The proof fixes a vertex and studies its local Gram lattice. This lattice
embeds in a positive-definite odd unimodular lattice of rank 15. Splitting off
norm-one directions and classifying the norm-two root system leaves five host
cases. The `ℤ¹⁵` and `E₈ ⊕ ℤ⁷` cases are ruled out structurally. The `D₁₂⁺`
case and two `A₁₅⁺` endpoints give binary weight-three factorizations, which
would produce a quasi-symmetric `2-(56, 12, 9)` design with block intersections
`0` and `3`. The `(E₇ ⊕ E₇)⁺` case and the other `A₁₅⁺` endpoints are excluded
by kernel-checked finite enumeration and exact arithmetic arguments.

Deleting a point and dualizing the 45 resulting traces gives a
`2-(45, 9, 2)` design. Its 55-block graph is the triangular graph `T(11)`, so
the design can be expressed as a cherry cover of `K₁₁`. The induced residual
structure yields a finite rational feasibility problem. Exact Hall cuts and
integer dual certificates, checked by Lean, refute every rooted normal form.

The final theorem uses only the three standard axioms routinely used by
Mathlib:

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
| `certificates/root_cubic_prefix/` | LRAT traces consumed by the cubic-prefix certificate modules |
| `scripts/shards.py` | CI sharding and lightweight closure audit |
| `scripts/print_axioms.lean` | axiom report |
| `docs/Literature.md` | relation to prior mathematical results |
| `CITATION.cff` | citation metadata |

## Verification

The lightweight audit reads the import graph, scans the 15,050-module closure,
and checks that every `include_str` input is present inside the repository,
without running Lean:

```bash
python3 scripts/shards.py audit
```

Release `v1.1.0` also provides the complete project olean closure produced by
the successful source build.  After checking out that tag, it can be replayed
through a fresh Lean kernel environment without repeating source elaboration:

```bash
lake exe cache get
archive=srg266-v1.1.0-lean4.32.2-oleans.tar.zst
release=https://github.com/kay-akiyama/srg266-nonexistence-lean/releases/download/v1.1.0
curl -LO "$release/$archive"
curl -LO "$release/$archive.sha256"
sha256sum --check "$archive.sha256"
mkdir -p .lake/build/lib/lean
zstd -dc "$archive" | tar -C .lake/build/lib/lean -x
lake env leanchecker --fresh SRG266.FractionalNearFrameMain
lake env lean scripts/print_axioms.lean
```

The accompanying `srg266-olean-manifest.json` records the source commit,
toolchain, Lake manifest hash, module count, producing workflow, and archive
digest.  `leanchecker --fresh` replays every declaration in the imported
environment through the Lean kernel; it does not re-elaborate the tagged
source files.  A full source-to-proof reproduction therefore uses the more
expensive clean build:

```bash
lake exe cache get
lake build
lake env lean scripts/print_axioms.lean
```

The full project takes roughly 140 CPU-hours. Individual certificate checks
can peak near 6 GB of memory, and part of the final assembly can approach
10 GB. An unrestricted parallel `lake build` may therefore exhaust memory.
The manually dispatched CI workflow rebuilds all project modules from source
against the pinned, prebuilt Mathlib cache. Its first stage uses twenty
balanced jobs; a second eleven-job stage consumes those artifacts to build the
independent dispatchers and side branches. Within each job, its
dependency-aware scheduler runs two ordinary targets concurrently only when
their unbuilt import closures are disjoint, while the memory-heavy dispatchers
remain serial inside each runner. The final job assembles only the dependent
tail, checks the headline theorem's axioms, and packages the 15,050 project
oleans. When the workflow is launched for an existing Release tag, a final
least-privilege job attaches the archive, checksum, and provenance manifest to
that Release. Maintainers first create the tag and draft Release, then run the
workflow with both `source_ref` and `release_tag` set to that tag. Leaving
`release_tag` empty performs the same verification but keeps the bundle as a
90-day workflow artifact instead of publishing it.

The certificate-generation tools and exploratory search artifacts are not part
of this release. The committed certificates are proof data: their validity is
replayed by Lean and does not depend on trusting the programs that found them.

## Author and citation

Author and maintainer: Kay Akiyama.

Citation metadata is provided in [`CITATION.cff`](CITATION.cff). GitHub exposes
it through the repository's **Cite this repository** action.

## LLM involvement

This project is the result of LLM-led mathematical research and formalization.
Kay Akiyama supplied the problem and the instruction to solve it. The
mathematical research was led mainly by GPT-5.6 Sol, with Claude Fable 5 used
as a second-opinion and discussion partner. The Lean formalization was done
mainly with Claude Opus 5 + Claude Code, with some parts developed using
GPT-5.6 Sol + Codex. The agents are not listed as authors. The formal result
does not rely on trusting them: the complete proof term is checked by the Lean
kernel, subject only to the three axioms listed above.

## Licence

Apache 2.0. See [`LICENSE`](LICENSE).
