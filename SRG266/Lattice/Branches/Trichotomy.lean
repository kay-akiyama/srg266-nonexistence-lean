/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.AuditedHostReduction

/-!
# The pure/mixed dichotomy

Every rank-15 embedding witness falls into exactly one of two cases:

* **pure** — `SRG266.Rank15EmbeddingWitness.NormOneDirectionsOrthogonal`, every
  norm-one host direction is orthogonal to every embedded generator, which is
  the hypothesis the three coordinate branches
  (`SRG266/Lattice/Branches/{D12,A15,E7E7}.lean`) and the two coreless branches
  (`SRG266/Lattice/Branches/Trivial.lean`) consume;
* **mixed** — some norm-one host direction pairs nontrivially with some
  generator, which is precisely the payload of the `mixedNormOne` constructor of
  `SRG266.AuditedRank15HostCase`.

The decision is free: the two cases are complementary, so `Classical.em`
supplies it.  What this file adds is the *shape* in which the mixed case is
delivered, namely the predicate

`SRG266.Rank15EmbeddingWitness.HasMixedNormOneDirection`,

which bundles the four non-`embedding` fields of `mixedNormOne`
(`SRG266/AuditedHostReduction.lean`) as one proposition about the embedding
alone.

That packaging is what a proof of `Rank15PreEnumerationNormalizationInput` needs:
`SRG266.Lattice.normOneDirectionsOrthogonal_or_hostCase` reduces that input to
its pure half, and the mixed half is discharged with no further work.  The
single `mixedNormOne` constructor splits into `mixedE7`
(carrying normalized shell coordinates and a listed key) and `mixedOtherHost`,
whose fields are exactly the fields of `HasMixedNormOneDirection`.
-/

namespace SRG266

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {x : V}

/-- **The mixed case of the trichotomy**, as a proposition about the embedding.

This is the payload of `SRG266.AuditedRank15HostCase.mixedNormOne` with the
`embedding` field abstracted: a norm-one host direction and a generator that the
direction does not annihilate.  It is the exact negation of
`SRG266.Rank15EmbeddingWitness.NormOneDirectionsOrthogonal`
(`SRG266.Lattice.hasMixedNormOneDirection_iff_not_normOneDirectionsOrthogonal`). -/
def Rank15EmbeddingWitness.HasMixedNormOneDirection
    (E : Rank15EmbeddingWitness G x) : Prop :=
  ∃ direction : E.host.carrier,
    E.host.pairing direction direction = 1 ∧
      ∃ generator : SecondSubconstituent G x,
        E.directionProfile (G := G) direction generator ≠ 0

namespace Lattice

/-- The mixed case is the negation of the pure case. -/
theorem hasMixedNormOneDirection_iff_not_normOneDirectionsOrthogonal
    (E : Rank15EmbeddingWitness G x) :
    E.HasMixedNormOneDirection ↔ ¬E.NormOneDirectionsOrthogonal G := by
  classical
  constructor
  · rintro ⟨direction, hdirection, generator, hgenerator⟩ hpure
    exact hgenerator (hpure direction hdirection generator)
  · intro hmixed
    by_contra hnone
    exact hmixed fun direction hdirection generator => by
      by_contra hgenerator
      exact hnone ⟨direction, hdirection, generator, hgenerator⟩

/-- An embedding witness is either pure — the
hypothesis of every coordinate branch — or mixed, and the mixed alternative
carries the payload of `SRG266.AuditedRank15HostCase.mixedNormOne`. -/
theorem normOneDirectionsOrthogonal_or_mixed (E : Rank15EmbeddingWitness G x) :
    E.NormOneDirectionsOrthogonal G ∨ E.HasMixedNormOneDirection := by
  classical
  by_cases hpure : E.NormOneDirectionsOrthogonal G
  · exact Or.inl hpure
  · exact Or.inr
      ((hasMixedNormOneDirection_iff_not_normOneDirectionsOrthogonal E).mpr hpure)

/-- The two cases are mutually exclusive, so the disjunction of
`SRG266.Lattice.normOneDirectionsOrthogonal_or_mixed` is exclusive. -/
theorem not_hasMixedNormOneDirection_of_normOneDirectionsOrthogonal
    {E : Rank15EmbeddingWitness G x} (hpure : E.NormOneDirectionsOrthogonal G) :
    ¬E.HasMixedNormOneDirection := fun hmixed =>
  ((hasMixedNormOneDirection_iff_not_normOneDirectionsOrthogonal E).mp hmixed) hpure

variable (G) in
/-- **The mixed case already answers the pre-enumeration input.**  It is
delivered by the `mixedNormOne` constructor unchanged, and separated out again
by `SRG266.MixedNormOneDirectionExclusionInput`. -/
theorem auditedRank15HostCase_of_hasMixedNormOneDirection
    {E : Rank15EmbeddingWitness G x} (hmixed : E.HasMixedNormOneDirection) :
    Nonempty (AuditedRank15HostCase G x) := by
  obtain ⟨direction, hdirection, generator, hgenerator⟩ := hmixed
  exact ⟨.mixedNormOne E direction hdirection generator hgenerator⟩

variable (G) in
/-- **What is left of `Rank15PreEnumerationNormalizationInput` after the
dichotomy.**  Either the embedding is pure — and the classification of the
norm-one-free core takes over — or the audited host case is already available.

This is the entry point the branch modules are written against: a proof of the
input needs only the pure half. -/
theorem normOneDirectionsOrthogonal_or_hostCase (E : Rank15EmbeddingWitness G x) :
    E.NormOneDirectionsOrthogonal G ∨ Nonempty (AuditedRank15HostCase G x) :=
  (normOneDirectionsOrthogonal_or_mixed E).imp id
    (auditedRank15HostCase_of_hasMixedNormOneDirection G)

end Lattice
end SRG266
