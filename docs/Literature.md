# Literature and provenance

This note records how the formal proof relates to published mathematics.
Bibliographic data is in [`references.bib`](references.bib). The citations are
context only: no result from the literature is introduced as an axiom or an
unproved hypothesis.

## Relation to the known nonexistence result

Munemasa and Tonchev (`MunemasaTonchev2020`, Theorem 7(i)) proved that no
quasi-symmetric `2-(56, 12, 9)` design has block intersections `0` and `3`.
The lattice reduction in this repository reaches the same design-theoretic
statement. The subsequent proof is independent of their biplane and ternary-code
argument: it identifies the derived block graph with `T(11)`, passes to cherry
covers of `K₁₁`, and eliminates the residual structures by exact rational
certificates.

## Classical results proved inside the development

Connor (`Connor1958`) proved the uniqueness of the triangular association
scheme in the range containing `T(11)`. The required case is proved directly in
[`TriangularUniqueness.lean`](../SRG266/QuasiSymmetric/TriangularUniqueness.lean)
and applied in
[`TriangularIso.lean`](../SRG266/QuasiSymmetric/TriangularIso.lean).

The rank-15 odd unimodular embedding is the relevant instance of the lattice
embedding results of Conway--Sloane (`ConwaySloane1989`) and Yang--Yoshino
(`YangYoshino2022`). Rather than importing that theorem as an assumption,
[`YangYoshino.lean`](../SRG266/Lattice/YangYoshino.lean) proves the instance for
the local Gram lattice using explicit finite complement data.

## Proof-specific reduction

[`SemanticBridge.lean`](../SRG266/QuasiSymmetric/SemanticBridge.lean) proves that
nonexistence of the quasi-symmetric design is equivalent to nonexistence of a
residual cherry cover. The latter is reduced to fractional near-frame
feasibility and discharged by kernel-checked Hall cuts and integer dual
certificates in
[`Certificates/FractionalNearFrame/`](../SRG266/Certificates/FractionalNearFrame/).

The final result is
[`SRG266.srg266_nonexistence`](../SRG266/FractionalNearFrameMain.lean). Its axiom
report contains only Lean's standard classical axioms; see
[`scripts/print_axioms.lean`](../scripts/print_axioms.lean).
