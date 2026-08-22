/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.QuasiSymmetric.RootOrbitCertificate

/-!
# Prefix-compositional cubic cover certificates

Large LRAT orbit-cover traces can exceed a bounded elaboration heap even when
the SAT instance is tiny.  This module provides a semantic leaf theorem and a
binary composition rule.  A generator may refine only the expensive low-bit
prefixes, while Lean checks each small LRAT leaf and reconstructs the complete
cover by ordinary theorems.
-/

namespace SRG266.QuasiSymmetric

open SRG266.Search

/-- Every bounded cubic mask with the specified low bits occurs in `masks`. -/
def CubicPrefixCovered (masks : List ℕ) (prefixBits prefixMask : ℕ) : Prop :=
  ∀ {mask : ℕ}, mask < 2 ^ 28 → IsCubic8 mask →
    (∀ i < prefixBits, mask.testBit i = prefixMask.testBit i) →
      mask ∈ masks

/-- One kernel-checked LRAT leaf establishes a prefix-cover statement for its
parent declarative list. -/
theorem cubicPrefixCovered_of_unsat
    (masks : List ℕ) (prefixBits prefixMask : ℕ)
    (hmasks : ∀ candidate ∈ masks, candidate < 2 ^ 28)
    (hunsat : (exactCountCoverChunkFmla 28 prefixBits prefixMask
      cubic8Constraints
      (masks.filter fun candidate =>
        candidate % 2 ^ prefixBits == prefixMask)).proof []) :
    CubicPrefixCovered masks prefixBits prefixMask := by
  intro mask hlt hcubic hbits
  have hmem := mem_cubicMasks_of_prefix_unsat prefixBits prefixMask
    (masks.filter fun candidate =>
      candidate % 2 ^ prefixBits == prefixMask)
    (fun candidate hcandidate => hmasks candidate
      (List.mem_of_mem_filter hcandidate))
    hunsat hlt hcubic hbits
  exact List.mem_of_mem_filter hmem

/-- Merge the two assignments of the next low bit.  The arithmetic side
condition is exactly the canonical-prefix invariant maintained by the
generator. -/
theorem CubicPrefixCovered.split
    {masks : List ℕ} {prefixBits prefixMask : ℕ}
    (hprefix : prefixMask < 2 ^ prefixBits)
    (hlow : CubicPrefixCovered masks (prefixBits + 1) prefixMask)
    (hhigh : CubicPrefixCovered masks (prefixBits + 1)
      (2 ^ prefixBits + prefixMask)) :
    CubicPrefixCovered masks prefixBits prefixMask := by
  intro mask hlt hcubic hbits
  by_cases hbit : mask.testBit prefixBits = true
  · apply hhigh hlt hcubic
    intro i hi
    by_cases hilow : i < prefixBits
    · rw [Nat.testBit_two_pow_add_gt hilow]
      exact hbits i hilow
    · have hieq : i = prefixBits := by omega
      subst i
      rw [hbit, Nat.testBit_two_pow_add_eq,
        Nat.testBit_lt_two_pow hprefix]
      rfl
  · apply hlow hlt hcubic
    intro i hi
    by_cases hilow : i < prefixBits
    · exact hbits i hilow
    · have hieq : i = prefixBits := by omega
      subst i
      rw [Bool.eq_false_of_not_eq_true hbit,
        Nat.testBit_lt_two_pow hprefix]

/-- A stronger prefix cover retaining a checked orbit witness for every
cubic mask.  This single relation supports both the reusable master list and
the six-representative orbit classification. -/
def CubicWitnessPrefixCovered (witnesses : List CubicOrbitWitness)
    (prefixBits prefixMask : ℕ) : Prop :=
  ∀ {mask : ℕ}, mask < 2 ^ 28 → IsCubic8 mask →
    (∀ i < prefixBits, mask.testBit i = prefixMask.testBit i) →
      ∃ witness ∈ witnesses,
        witness.mask = mask ∧ checkCubicOrbitWitness witness = true

/-- An LRAT leaf plus the Boolean witness checks gives the strong witnessed
prefix relation. -/
theorem cubicWitnessPrefixCovered_of_unsat
    (witnesses : List CubicOrbitWitness) (prefixBits prefixMask : ℕ)
    (hcheck : (witnesses.filter fun witness =>
      witness.mask % 2 ^ prefixBits == prefixMask).all
        checkCubicOrbitWitness = true)
    (hunsat : (exactCountCoverChunkFmla 28 prefixBits prefixMask
      cubic8Constraints
      ((witnesses.filter fun witness =>
        witness.mask % 2 ^ prefixBits == prefixMask).map
          CubicOrbitWitness.mask)).proof []) :
    CubicWitnessPrefixCovered witnesses prefixBits prefixMask := by
  intro mask hlt hcubic hbits
  let leafWitnesses := witnesses.filter fun witness =>
    witness.mask % 2 ^ prefixBits == prefixMask
  have hbounded : ∀ candidate ∈ leafWitnesses.map CubicOrbitWitness.mask,
      candidate < 2 ^ 28 := by
    intro candidate hcandidate
    obtain ⟨witness, hwitness, rfl⟩ := List.mem_map.mp hcandidate
    exact (CubicOrbitWitness.of_check
      ((List.all_eq_true.mp hcheck) witness hwitness)).1
  have hmem := mem_cubicMasks_of_prefix_unsat prefixBits prefixMask
    (leafWitnesses.map CubicOrbitWitness.mask) hbounded hunsat
    hlt hcubic hbits
  obtain ⟨witness, hwitness, heq⟩ := List.mem_map.mp hmem
  exact ⟨witness, List.mem_of_mem_filter hwitness, heq,
    (List.all_eq_true.mp hcheck) witness hwitness⟩

/-- Binary prefix composition for the witnessed relation. -/
theorem CubicWitnessPrefixCovered.split
    {witnesses : List CubicOrbitWitness} {prefixBits prefixMask : ℕ}
    (hprefix : prefixMask < 2 ^ prefixBits)
    (hlow : CubicWitnessPrefixCovered witnesses (prefixBits + 1) prefixMask)
    (hhigh : CubicWitnessPrefixCovered witnesses (prefixBits + 1)
      (2 ^ prefixBits + prefixMask)) :
    CubicWitnessPrefixCovered witnesses prefixBits prefixMask := by
  intro mask hlt hcubic hbits
  by_cases hbit : mask.testBit prefixBits = true
  · apply hhigh hlt hcubic
    intro i hi
    by_cases hilow : i < prefixBits
    · rw [Nat.testBit_two_pow_add_gt hilow]
      exact hbits i hilow
    · have hieq : i = prefixBits := by omega
      subst i
      rw [hbit, Nat.testBit_two_pow_add_eq,
        Nat.testBit_lt_two_pow hprefix]
      rfl
  · apply hlow hlt hcubic
    intro i hi
    by_cases hilow : i < prefixBits
    · exact hbits i hilow
    · have hieq : i = prefixBits := by omega
      subst i
      rw [Bool.eq_false_of_not_eq_true hbit,
        Nat.testBit_lt_two_pow hprefix]

end SRG266.QuasiSymmetric
