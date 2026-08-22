/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Certificates.A15FinalTransportBase
import SRG266.Hosts.A15FinalTransportBridge

/-!
# Structural orbit identifications for the final A15 transport

The compact projector membership certificates already prove that every
eligible four-subset lies in exactly one reported orbit. The four surviving
profiles have two orbits, distinguished by whether their singleton coordinate
class is selected. This identifies the final transport predicates without a
second exhaustive pass over all 1,820 four-subsets.
-/

namespace SRG266

private theorem a15SubsetContains_of_singletonClassCount_one
    (profile : A15ProjectorProfile)
    (k : Fin profile.orbits.size)
    (c : Fin profile.classSizes.size)
    (i : Fin 16)
    (hclass : profile.classFinset c.1 = {i})
    (horbit : profile.orbitClassCount k.1 c.1 = 1)
    (s : A15EligibleIndex profile.centroidVector)
    (hmatch : profile.indexMatches k.1 s.1) :
    a15SubsetContains s i := by
  have hcount :=
    A15ProjectorProfile.indexMatches_classCount profile k c s.1 hmatch
  have hcard :
      (profile.classFinset c.1 ∩ a15FourSubsetAsFinset s.1).card = 1 := by
    rw [← a15ProjectorClassCount_eq_card]
    exact hcount.symm.trans horbit
  rw [hclass] at hcard
  by_contra hcontains
  have hempty : {i} ∩ a15FourSubsetAsFinset s.1 = ∅ := by
    ext j
    simp [a15SubsetContains] at hcontains
    simp [hcontains]
  rw [hempty] at hcard
  simp at hcard

private theorem not_a15SubsetContains_of_singletonClassCount_zero
    (profile : A15ProjectorProfile)
    (k : Fin profile.orbits.size)
    (c : Fin profile.classSizes.size)
    (i : Fin 16)
    (hclass : profile.classFinset c.1 = {i})
    (horbit : profile.orbitClassCount k.1 c.1 = 0)
    (s : A15EligibleIndex profile.centroidVector)
    (hmatch : profile.indexMatches k.1 s.1) :
    ¬a15SubsetContains s i := by
  have hcount :=
    A15ProjectorProfile.indexMatches_classCount profile k c s.1 hmatch
  have hcard :
      (profile.classFinset c.1 ∩ a15FourSubsetAsFinset s.1).card = 0 := by
    rw [← a15ProjectorClassCount_eq_card]
    exact hcount.symm.trans horbit
  rw [hclass] at hcard
  intro hcontains
  have hmem : i ∈ {i} ∩ a15FourSubsetAsFinset s.1 := by
    exact Finset.mem_inter.mpr ⟨by simp, hcontains⟩
  rw [Finset.card_eq_zero.mp hcard] at hmem
  simp at hmem

private theorem indexMatches_zero_of_unique_pair
    (profile : A15ProjectorProfile)
    (hsize : profile.orbits.size = 2)
    (hunique : ∀ s : A15FourSubsetIndex,
      a15Eligible profile.centroidVector s → profile.indexMatchCount s = 1)
    (s : A15EligibleIndex profile.centroidVector)
    (hnot : ¬profile.indexMatches 1 s.1) :
    profile.indexMatches 0 s.1 := by
  have hcard := hunique s.1 s.2
  change
    (Finset.univ.filter fun k : Fin profile.orbits.size =>
      profile.indexMatches k.1 s.1).card = 1 at hcard
  have hnonempty :
      (Finset.univ.filter fun k : Fin profile.orbits.size =>
        profile.indexMatches k.1 s.1).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨k, hk⟩ := hnonempty
  have hmatch := (Finset.mem_filter.mp hk).2
  have hklt := k.isLt
  have hkltTwo : k.1 < 2 := by omega
  by_cases hkzero : k.1 = 0
  · simpa [hkzero] using hmatch
  · have hkone : k.1 = 1 := by omega
    exact (hnot (by simpa [hkone] using hmatch)).elim

private theorem indexMatches_one_of_unique_pair
    (profile : A15ProjectorProfile)
    (hsize : profile.orbits.size = 2)
    (hunique : ∀ s : A15FourSubsetIndex,
      a15Eligible profile.centroidVector s → profile.indexMatchCount s = 1)
    (s : A15EligibleIndex profile.centroidVector)
    (hnot : ¬profile.indexMatches 0 s.1) :
    profile.indexMatches 1 s.1 := by
  have hcard := hunique s.1 s.2
  change
    (Finset.univ.filter fun k : Fin profile.orbits.size =>
      profile.indexMatches k.1 s.1).card = 1 at hcard
  have hnonempty :
      (Finset.univ.filter fun k : Fin profile.orbits.size =>
        profile.indexMatches k.1 s.1).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨k, hk⟩ := hnonempty
  have hmatch := (Finset.mem_filter.mp hk).2
  have hklt := k.isLt
  have hkltTwo : k.1 < 2 := by omega
  by_cases hkzero : k.1 = 0
  · exact (hnot (by simpa [hkzero] using hmatch)).elim
  · have hkone : k.1 = 1 := by omega
    simpa [hkone] using hmatch

private theorem a15ProjectorProfile00_classFinset_zero :
    a15ProjectorProfile00.profile.classFinset 0 = {0} := by
  ext i
  fin_cases i <;> decide +kernel

private theorem a15ProjectorProfile01_classFinset_three :
    a15ProjectorProfile01.profile.classFinset 3 = {15} := by
  ext i
  fin_cases i <;> decide +kernel

private theorem a15ProjectorProfile08_classFinset_zero :
    a15ProjectorProfile08.profile.classFinset 0 = {0} := by
  ext i
  fin_cases i <;> decide +kernel

private theorem a15ProjectorProfile12_classFinset_two :
    a15ProjectorProfile12.profile.classFinset 2 = {15} := by
  ext i
  fin_cases i <;> decide +kernel

theorem a15ProjectorProfile00_orbit0_iff
    (s : A15EligibleIndex
      a15ProjectorProfile00.profile.centroidVector) :
    a15ProjectorProfile00.profile.indexMatches 0 s.1 ↔
      ¬a15SubsetContains
        (a15ProjectorProfile00_centroidVector ▸ s) 0 := by
  rw [a15SubsetContains_transport]
  have hbridge : a15ProjectorProfile00.profile.bridgeValid :=
    a15ProjectorProfile00_bridgeValid
  rcases hbridge with ⟨_, _, _, _, _, _, _, hunique, _⟩
  constructor
  · exact not_a15SubsetContains_of_singletonClassCount_zero
      a15ProjectorProfile00.profile
      ⟨0, by decide⟩ ⟨0, by decide⟩ 0
      a15ProjectorProfile00_classFinset_zero (by rfl) s
  · intro hnot
    apply indexMatches_zero_of_unique_pair
      a15ProjectorProfile00.profile (by rfl) hunique s
    intro hmatch
    exact hnot (a15SubsetContains_of_singletonClassCount_one
      a15ProjectorProfile00.profile
      ⟨1, by decide⟩ ⟨0, by decide⟩ 0
      a15ProjectorProfile00_classFinset_zero (by rfl) s hmatch)

theorem a15ProjectorProfile01_orbit0_iff
    (s : A15EligibleIndex
      a15ProjectorProfile01.profile.centroidVector) :
    a15ProjectorProfile01.profile.indexMatches 0 s.1 ↔
      a15SubsetContains
        (a15ProjectorProfile01_centroidVector ▸ s) 15 := by
  rw [a15SubsetContains_transport]
  have hbridge : a15ProjectorProfile01.profile.bridgeValid :=
    a15ProjectorProfile01_bridgeValid
  rcases hbridge with ⟨_, _, _, _, _, _, _, hunique, _⟩
  constructor
  · exact a15SubsetContains_of_singletonClassCount_one
      a15ProjectorProfile01.profile
      ⟨0, by decide⟩ ⟨3, by decide⟩ 15
      a15ProjectorProfile01_classFinset_three (by rfl) s
  · intro hcontains
    apply indexMatches_zero_of_unique_pair
      a15ProjectorProfile01.profile (by rfl) hunique s
    intro hmatch
    exact (not_a15SubsetContains_of_singletonClassCount_zero
      a15ProjectorProfile01.profile
      ⟨1, by decide⟩ ⟨3, by decide⟩ 15
      a15ProjectorProfile01_classFinset_three (by rfl) s hmatch) hcontains

theorem a15ProjectorProfile01_orbit0_cast_iff
    (s : A15EligibleIndex
      a15ProjectorProfile01.profile.centroidVector) :
    a15ProjectorProfile01.profile.indexMatches 0 s.1 ↔
      a15SubsetContains
        (Equiv.cast
          (congrArg A15EligibleIndex
            a15ProjectorProfile01_centroidVector) s) 15 := by
  exact (a15ProjectorProfile01_orbit0_iff s).trans
    ((a15SubsetContains_transport
      a15ProjectorProfile01_centroidVector s 15).trans
    (a15SubsetContains_equivCast
      a15ProjectorProfile01_centroidVector s 15).symm)

theorem a15ProjectorProfile08_orbit1_iff
    (s : A15EligibleIndex
      a15ProjectorProfile08.profile.centroidVector) :
    a15ProjectorProfile08.profile.indexMatches 1 s.1 ↔
      a15SubsetContains
        (a15ProjectorProfile08_centroidVector ▸ s) 0 := by
  rw [a15SubsetContains_transport]
  have hbridge : a15ProjectorProfile08.profile.bridgeValid :=
    a15ProjectorProfile08_bridgeValid
  rcases hbridge with ⟨_, _, _, _, _, _, _, hunique, _⟩
  constructor
  · exact a15SubsetContains_of_singletonClassCount_one
      a15ProjectorProfile08.profile
      ⟨1, by decide⟩ ⟨0, by decide⟩ 0
      a15ProjectorProfile08_classFinset_zero (by rfl) s
  · intro hcontains
    apply indexMatches_one_of_unique_pair
      a15ProjectorProfile08.profile (by rfl) hunique s
    intro hmatch
    exact (not_a15SubsetContains_of_singletonClassCount_zero
      a15ProjectorProfile08.profile
      ⟨0, by decide⟩ ⟨0, by decide⟩ 0
      a15ProjectorProfile08_classFinset_zero (by rfl) s hmatch) hcontains

theorem a15ProjectorProfile08_orbit1_cast_iff
    (s : A15EligibleIndex
      a15ProjectorProfile08.profile.centroidVector) :
    a15ProjectorProfile08.profile.indexMatches 1 s.1 ↔
      a15SubsetContains
        (Equiv.cast
          (congrArg A15EligibleIndex
            a15ProjectorProfile08_centroidVector) s) 0 := by
  exact (a15ProjectorProfile08_orbit1_iff s).trans
    ((a15SubsetContains_transport
      a15ProjectorProfile08_centroidVector s 0).trans
    (a15SubsetContains_equivCast
      a15ProjectorProfile08_centroidVector s 0).symm)

theorem a15ProjectorProfile12_orbit1_iff
    (s : A15EligibleIndex
      a15ProjectorProfile12.profile.centroidVector) :
    a15ProjectorProfile12.profile.indexMatches 1 s.1 ↔
      ¬a15SubsetContains
        (a15ProjectorProfile12_centroidVector ▸ s) 15 := by
  rw [a15SubsetContains_transport]
  have hbridge : a15ProjectorProfile12.profile.bridgeValid :=
    a15ProjectorProfile12_bridgeValid
  rcases hbridge with ⟨_, _, _, _, _, _, _, hunique, _⟩
  constructor
  · exact not_a15SubsetContains_of_singletonClassCount_zero
      a15ProjectorProfile12.profile
      ⟨1, by decide⟩ ⟨2, by decide⟩ 15
      a15ProjectorProfile12_classFinset_two (by rfl) s
  · intro hnot
    apply indexMatches_one_of_unique_pair
      a15ProjectorProfile12.profile (by rfl) hunique s
    intro hmatch
    exact hnot (a15SubsetContains_of_singletonClassCount_one
      a15ProjectorProfile12.profile
      ⟨0, by decide⟩ ⟨2, by decide⟩ 15
      a15ProjectorProfile12_classFinset_two (by rfl) s hmatch)

end SRG266
