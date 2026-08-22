/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.QuasiSymmetric.RootOrbitCoordinates

/-!
# Declarative witnesses for the rooted orbit cover

Generators emit only values of the structures in this file.  The Boolean
checkers establish range, permutation, representative-membership, and exact
relabel equations; their soundness lemmas expose those facts as ordinary Lean
propositions.  No generator status or aggregate count is trusted.
-/

namespace SRG266.QuasiSymmetric

/-- One labelled cubic graph together with its orbit witness. -/
structure CubicOrbitWitness where
  mask : ℕ
  representative : ℕ
  permutationCode : ℕ
deriving DecidableEq

/-- Check every mathematical field of a cubic orbit witness. -/
def checkCubicOrbitWitness (witness : CubicOrbitWitness) : Bool :=
  decide (witness.mask < 2 ^ 28) &&
    decide (witness.representative ∈ rootGraphRepresentatives) &&
      decide (PackedPerm8OK witness.permutationCode) &&
        (witness.mask ==
          relabelEdgeMask8 witness.permutationCode witness.representative)

theorem CubicOrbitWitness.of_check {witness : CubicOrbitWitness}
    (hcheck : checkCubicOrbitWitness witness = true) :
    witness.mask < 2 ^ 28 ∧
      witness.representative ∈ rootGraphRepresentatives ∧
        PackedPerm8OK witness.permutationCode ∧
          witness.mask =
            relabelEdgeMask8 witness.permutationCode witness.representative := by
  have h := hcheck
  simp only [checkCubicOrbitWitness, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  rcases h with ⟨⟨⟨hmask, hrep⟩, hperm⟩, heq⟩
  exact ⟨hmask, hrep, hperm, heq⟩

/-- One fixed-root near mask together with a representative and a root-graph
automorphism carrying that representative to the labelled mask. -/
structure NearOrbitWitness where
  mask : ℕ
  representativeIndex : ℕ
  representative : ℕ
  permutationCode : ℕ
deriving DecidableEq

/-- Check a near witness relative to one canonical root graph and its indexed
representative group.  The redundant representative value keeps generated
records readable; the array lookup prevents a linear membership scan for every
labelled mask. -/
def checkNearOrbitWitness (rootGraph : ℕ) (representatives : Array ℕ)
    (witness : NearOrbitWitness) : Bool :=
  decide (witness.mask < 2 ^ 56) &&
    (representatives[witness.representativeIndex]? ==
      some witness.representative) &&
      decide (PackedPerm8OK witness.permutationCode) &&
        (relabelEdgeMask8 witness.permutationCode rootGraph == rootGraph) &&
          (witness.mask == relabelTripleMask8 witness.permutationCode
            witness.representative)

theorem NearOrbitWitness.of_check {rootGraph : ℕ}
    {representatives : Array ℕ}
    {witness : NearOrbitWitness}
    (hcheck : checkNearOrbitWitness rootGraph representatives witness = true) :
    witness.mask < 2 ^ 56 ∧
      representatives[witness.representativeIndex]? =
        some witness.representative ∧
        PackedPerm8OK witness.permutationCode ∧
          relabelEdgeMask8 witness.permutationCode rootGraph = rootGraph ∧
            witness.mask = relabelTripleMask8 witness.permutationCode
              witness.representative := by
  have h := hcheck
  simp only [checkNearOrbitWitness, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  rcases h with ⟨⟨⟨⟨hmask, hrep⟩, hperm⟩, hroot⟩, heq⟩
  exact ⟨hmask, hrep, hperm, hroot, heq⟩

/-- A checked LRAT chunk covers every exact-count model having its fixed low
bits. -/
theorem mem_cubicOrbitMasks_of_chunk_unsat
    (prefixMask : ℕ) (witnesses : List CubicOrbitWitness)
    (hcheck : witnesses.all checkCubicOrbitWitness = true)
    (hunsat : (cubic8CoverChunkFmla prefixMask
      (witnesses.map CubicOrbitWitness.mask)).proof [])
    {mask : ℕ} (hlt : mask < 2 ^ 28) (hcubic : IsCubic8 mask)
    (hbits : ∀ i < 4, mask.testBit i = prefixMask.testBit i) :
    mask ∈ witnesses.map CubicOrbitWitness.mask := by
  by_contra hnot
  have hmasks : ∀ candidate ∈ witnesses.map CubicOrbitWitness.mask,
      candidate < 2 ^ 28 := by
    intro candidate hcandidate
    obtain ⟨witness, hwitness, rfl⟩ := List.mem_map.mp hcandidate
    have hall := (List.all_eq_true.mp hcheck) witness hwitness
    exact (CubicOrbitWitness.of_check hall).1
  exact SRG266.Search.false_of_lrat_and_evalFmla hunsat (fun i => mask.testBit i)
    (SRG266.Search.eval_exactCountCoverChunkFmla_eq_true
      hcubic hbits hlt hmasks hnot)

/-- A checked prefix LRAT leaf covers every cubic mask having the declared
low-bit assignment.  Unlike the orbit-witness wrapper above, this theorem
needs only a direct bound on the declarative mask list.  It is therefore
suitable for low-memory refinements of a large orbit chunk. -/
theorem mem_cubicMasks_of_prefix_unsat
    (prefixBits prefixMask : ℕ) (masks : List ℕ)
    (hmasks : ∀ candidate ∈ masks, candidate < 2 ^ 28)
    (hunsat : (SRG266.Search.exactCountCoverChunkFmla 28 prefixBits prefixMask
      cubic8Constraints masks).proof [])
    {mask : ℕ} (hlt : mask < 2 ^ 28) (hcubic : IsCubic8 mask)
    (hbits : ∀ i < prefixBits,
      mask.testBit i = prefixMask.testBit i) :
    mask ∈ masks := by
  by_contra hnot
  exact SRG266.Search.false_of_lrat_and_evalFmla hunsat
    (fun i => mask.testBit i)
    (SRG266.Search.eval_exactCountCoverChunkFmla_eq_true
      hcubic hbits hlt hmasks hnot)

/-- A checked fixed-root LRAT chunk covers every near exact-count model having
its fixed low bits. -/
theorem mem_nearOrbitMasks_of_chunk_unsat
    (rootGraph prefixBits prefixMask : ℕ) (representatives : Array ℕ)
    (witnesses : List NearOrbitWitness)
    (hcheck : witnesses.all
      (checkNearOrbitWitness rootGraph representatives) = true)
    (hunsat : (near8CoverChunkFmla rootGraph prefixBits prefixMask
      (witnesses.map NearOrbitWitness.mask)).proof [])
    {mask : ℕ} (hlt : mask < 2 ^ 56) (hnear : IsNear8For rootGraph mask)
    (hbits : ∀ i < prefixBits,
      mask.testBit i = prefixMask.testBit i) :
    mask ∈ witnesses.map NearOrbitWitness.mask := by
  by_contra hnot
  have hmasks : ∀ candidate ∈ witnesses.map NearOrbitWitness.mask,
      candidate < 2 ^ 56 := by
    intro candidate hcandidate
    obtain ⟨witness, hwitness, rfl⟩ := List.mem_map.mp hcandidate
    have hall := (List.all_eq_true.mp hcheck) witness hwitness
    exact (NearOrbitWitness.of_check hall).1
  exact SRG266.Search.false_of_lrat_and_evalFmla hunsat (fun i => mask.testBit i)
    (SRG266.Search.eval_exactCountCoverChunkFmla_eq_true
      hnear hbits hlt hmasks hnot)

end SRG266.QuasiSymmetric
