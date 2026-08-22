/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.QuasiSymmetric.RootOrbitCertificate

/-!
# Assembly lemmas for fixed-root near-orbit certificates

Each generated leaf fixes a low-bit prefix, validates every orbit witness, and
contains a kernel-checked LRAT refutation of any unlisted exact-count model.
This module converts one such leaf into an ordinary orbit-membership theorem.
-/

namespace SRG266.QuasiSymmetric

/-- Congruence modulo `2^width` determines every bit below `width`. -/
theorem testBit_eq_of_mod_two_pow {assignment prefixMask width : ℕ}
    (hmod : assignment % 2 ^ width = prefixMask) {i : ℕ} (hi : i < width) :
    assignment.testBit i = prefixMask.testBit i := by
  rw [← hmod]
  rw [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and]

/-- One checked prefix leaf produces a concrete representative and root-graph
automorphism for every model in that prefix. -/
theorem near8_orbit_cover_of_chunk
    (rootGraph prefixBits prefixMask : ℕ) (representatives : Array ℕ)
    (witnesses : List NearOrbitWitness)
    (hcheck : witnesses.all
      (checkNearOrbitWitness rootGraph representatives) = true)
    (hunsat : (near8CoverChunkFmla rootGraph prefixBits prefixMask
      (witnesses.map NearOrbitWitness.mask)).proof [])
    {mask : ℕ} (hlt : mask < 2 ^ 56) (hnear : IsNear8For rootGraph mask)
    (hbits : ∀ i < prefixBits,
      mask.testBit i = prefixMask.testBit i) :
    ∃ representative ∈ representatives,
      ∃ permutationCode,
        PackedPerm8OK permutationCode ∧
          relabelEdgeMask8 permutationCode rootGraph = rootGraph ∧
            mask = relabelTripleMask8 permutationCode representative := by
  have hmem : mask ∈ witnesses.map NearOrbitWitness.mask :=
    mem_nearOrbitMasks_of_chunk_unsat rootGraph prefixBits prefixMask
      representatives witnesses hcheck hunsat hlt hnear hbits
  obtain ⟨witness, hwitness, hwitnessMask⟩ := List.mem_map.mp hmem
  have hvalid := (List.all_eq_true.mp hcheck) witness hwitness
  obtain ⟨_, hlookup, hperm, hroot, heq⟩ :=
    NearOrbitWitness.of_check hvalid
  have hrepresentative : witness.representative ∈ representatives := by
    rw [Array.mem_iff_getElem]
    obtain ⟨hindex, hget⟩ := Array.getElem?_eq_some_iff.mp hlookup
    exact ⟨witness.representativeIndex, hindex, hget⟩
  exact ⟨witness.representative, hrepresentative,
    witness.permutationCode, hperm, hroot, hwitnessMask.symm.trans heq⟩

end SRG266.QuasiSymmetric
