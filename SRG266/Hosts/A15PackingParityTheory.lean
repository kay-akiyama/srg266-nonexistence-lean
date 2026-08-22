/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.A15Plus
import SRG266.Hosts.A15Parity

/-!
# Structural theory of the two A15 parity shells

The two sign-paired projector survivors are reduced to the triples of an
eight-element coordinate class. The proof uses exact coordinate partitions,
ordinary integer arithmetic, the checked four-subset universe, and explicit
inverse constructions. No executable decision over the full 1,820-entry
universe is used.
-/

namespace SRG266

open scoped BigOperators

/-- Membership of one coordinate in an eligible A15 four-subset. -/
def a15SubsetContains
    {d : Fin 16 → ℤ} (s : A15EligibleIndex d) (i : Fin 16) : Prop :=
  i ∈ a15FourSubsetAsFinset s.1

instance {d : Fin 16 → ℤ} (s : A15EligibleIndex d) (i : Fin 16) :
    Decidable (a15SubsetContains s i) := by
  unfold a15SubsetContains
  infer_instance

/-- The first sign-paired A15 projector survivor. -/
def a15ParityProfile1 : Fin 16 → ℤ :=
  ![-50, -10, -10, -10, -10, -10, -10,
    10, 10, 10, 10, 10, 10, 10, 10, 30]

/-- The sign-reversed companion at projector-survivor index 8. -/
def a15ParityProfile8 : Fin 16 → ℤ :=
  ![-30, -10, -10, -10, -10, -10, -10, -10, -10,
    10, 10, 10, 10, 10, 10, 50]

def a15ParityCoordinate1 (j : Fin 8) : Fin 16 :=
  ⟨j.1 + 7, by omega⟩

def a15ParityCoordinate8 (j : Fin 8) : Fin 16 :=
  ⟨j.1 + 1, by omega⟩

abbrev A15ParityBIndex1 :=
  {s : A15EligibleIndex a15ParityProfile1 //
    a15SubsetContains s 15}

abbrev A15ParityBIndex8 :=
  {s : A15EligibleIndex a15ParityProfile8 //
    a15SubsetContains s 0}

def a15ParitySupport1
    (s : A15EligibleIndex a15ParityProfile1) : Finset (Fin 8) :=
  Finset.univ.filter fun j =>
    a15ParityCoordinate1 j ∈ a15FourSubsetAsFinset s.1

def a15ParitySupport8
    (s : A15EligibleIndex a15ParityProfile8) : Finset (Fin 8) :=
  Finset.univ.filter fun j =>
    a15ParityCoordinate8 j ∈ a15FourSubsetAsFinset s.1

def scratchLow1 : Finset (Fin 16) :=
  Finset.univ.image fun j : Fin 6 => ⟨j.1 + 1, by omega⟩

def scratchHigh8 : Finset (Fin 16) :=
  Finset.univ.image fun j : Fin 6 => ⟨j.1 + 9, by omega⟩

def scratchY1 : Finset (Fin 16) :=
  Finset.univ.image a15ParityCoordinate1

def scratchY8 : Finset (Fin 16) :=
  Finset.univ.image a15ParityCoordinate8

private theorem scratch_profile1_apply (i : Fin 16) :
    a15ParityProfile1 i =
      (if i = 0 then -50 else 0) +
        (if i ∈ scratchLow1 then -10 else 0) +
        (if i ∈ scratchY1 then 10 else 0) +
        (if i = 15 then 30 else 0) := by
  fin_cases i <;> decide +kernel

private theorem scratch_profile8_apply (i : Fin 16) :
    a15ParityProfile8 i =
      (if i = 0 then -30 else 0) +
        (if i ∈ scratchY8 then -10 else 0) +
        (if i ∈ scratchHigh8 then 10 else 0) +
        (if i = 15 then 50 else 0) := by
  fin_cases i <;> decide +kernel

private theorem scratch_partition1_apply (i : Fin 16) :
    (1 : ℤ) =
      (if i = 0 then 1 else 0) +
        (if i ∈ scratchLow1 then 1 else 0) +
        (if i ∈ scratchY1 then 1 else 0) +
        (if i = 15 then 1 else 0) := by
  fin_cases i <;> decide +kernel

private theorem scratch_partition8_apply (i : Fin 16) :
    (1 : ℤ) =
      (if i = 0 then 1 else 0) +
        (if i ∈ scratchY8 then 1 else 0) +
        (if i ∈ scratchHigh8 then 1 else 0) +
        (if i = 15 then 1 else 0) := by
  fin_cases i <;> decide +kernel

private theorem scratch_sum_indicator
    (S C : Finset (Fin 16)) :
    (∑ i ∈ S, if i ∈ C then (1 : ℤ) else 0) = (S ∩ C).card := by
  simp

private theorem scratch_profile1_sum_formula
    (s : A15FourSubsetIndex) :
    let S := a15FourSubsetAsFinset s
    a15SubsetSum a15ParityProfile1 s =
      -50 * (if (0 : Fin 16) ∈ S then 1 else 0) -
        10 * (S ∩ scratchLow1).card +
        10 * (S ∩ scratchY1).card +
        30 * (if (15 : Fin 16) ∈ S then 1 else 0) := by
  dsimp only
  unfold a15SubsetSum a15DataSubsetSum
  rw [a15FourSubset_valueSum_eq_finset_sum]
  simp_rw [scratch_profile1_apply]
  simp only [Finset.sum_add_distrib]
  rw [show (∑ i ∈ a15FourSubsetAsFinset s,
      if i ∈ scratchLow1 then (-10 : ℤ) else 0) =
        -10 * ((a15FourSubsetAsFinset s ∩ scratchLow1).card : ℤ) by
      simp
      ring]
  rw [show (∑ i ∈ a15FourSubsetAsFinset s,
      if i ∈ scratchY1 then (10 : ℤ) else 0) =
        10 * ((a15FourSubsetAsFinset s ∩ scratchY1).card : ℤ) by
      simp
      ring]
  by_cases h0 : (0 : Fin 16) ∈ a15FourSubsetAsFinset s <;>
    by_cases h15 : (15 : Fin 16) ∈ a15FourSubsetAsFinset s <;>
    simp [h0, h15] <;> ring

private theorem scratch_profile1_count_formula
    (s : A15FourSubsetIndex) :
    let S := a15FourSubsetAsFinset s
    (4 : ℤ) =
      (if (0 : Fin 16) ∈ S then 1 else 0) +
        (S ∩ scratchLow1).card +
        (S ∩ scratchY1).card +
        (if (15 : Fin 16) ∈ S then 1 else 0) := by
  dsimp only
  have hcard : (a15FourSubsetAsFinset s).card = 4 := by
    unfold a15FourSubsetAsFinset A15FourSubset.asFinset
    rw [List.toFinset_card_of_nodup
      (a15FourSubsetAt_coordinates_nodup s)]
    rfl
  calc
    (4 : ℤ) = ∑ i ∈ a15FourSubsetAsFinset s, (1 : ℤ) := by
      simp [hcard]
    _ = ∑ i ∈ a15FourSubsetAsFinset s,
        ((if i = 0 then 1 else 0) +
          (if i ∈ scratchLow1 then 1 else 0) +
          (if i ∈ scratchY1 then 1 else 0) +
          (if i = 15 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact scratch_partition1_apply i
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      by_cases h0 : (0 : Fin 16) ∈ a15FourSubsetAsFinset s <;>
        by_cases h15 : (15 : Fin 16) ∈ a15FourSubsetAsFinset s <;>
        simp [h0, h15]

private theorem scratch_profile8_sum_formula
    (s : A15FourSubsetIndex) :
    let S := a15FourSubsetAsFinset s
    a15SubsetSum a15ParityProfile8 s =
      -30 * (if (0 : Fin 16) ∈ S then 1 else 0) -
        10 * (S ∩ scratchY8).card +
        10 * (S ∩ scratchHigh8).card +
        50 * (if (15 : Fin 16) ∈ S then 1 else 0) := by
  dsimp only
  unfold a15SubsetSum a15DataSubsetSum
  rw [a15FourSubset_valueSum_eq_finset_sum]
  simp_rw [scratch_profile8_apply]
  simp only [Finset.sum_add_distrib]
  rw [show (∑ i ∈ a15FourSubsetAsFinset s,
      if i ∈ scratchY8 then (-10 : ℤ) else 0) =
        -10 * ((a15FourSubsetAsFinset s ∩ scratchY8).card : ℤ) by
      simp
      ring]
  rw [show (∑ i ∈ a15FourSubsetAsFinset s,
      if i ∈ scratchHigh8 then (10 : ℤ) else 0) =
        10 * ((a15FourSubsetAsFinset s ∩ scratchHigh8).card : ℤ) by
      simp
      ring]
  by_cases h0 : (0 : Fin 16) ∈ a15FourSubsetAsFinset s <;>
    by_cases h15 : (15 : Fin 16) ∈ a15FourSubsetAsFinset s <;>
    simp [h0, h15] <;> ring

private theorem scratch_profile8_count_formula
    (s : A15FourSubsetIndex) :
    let S := a15FourSubsetAsFinset s
    (4 : ℤ) =
      (if (0 : Fin 16) ∈ S then 1 else 0) +
        (S ∩ scratchY8).card +
        (S ∩ scratchHigh8).card +
        (if (15 : Fin 16) ∈ S then 1 else 0) := by
  dsimp only
  have hcard : (a15FourSubsetAsFinset s).card = 4 := by
    unfold a15FourSubsetAsFinset A15FourSubset.asFinset
    rw [List.toFinset_card_of_nodup
      (a15FourSubsetAt_coordinates_nodup s)]
    rfl
  calc
    (4 : ℤ) = ∑ i ∈ a15FourSubsetAsFinset s, (1 : ℤ) := by
      simp [hcard]
    _ = ∑ i ∈ a15FourSubsetAsFinset s,
        ((if i = 0 then 1 else 0) +
          (if i ∈ scratchY8 then 1 else 0) +
          (if i ∈ scratchHigh8 then 1 else 0) +
          (if i = 15 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact scratch_partition8_apply i
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      by_cases h0 : (0 : Fin 16) ∈ a15FourSubsetAsFinset s <;>
        by_cases h15 : (15 : Fin 16) ∈ a15FourSubsetAsFinset s <;>
        simp [h0, h15]

private theorem scratch_profile1_anchor_facts
    (s : A15EligibleIndex a15ParityProfile1)
    (hs : a15SubsetContains s 15) :
    a15SubsetSum a15ParityProfile1 s.1 = 60 ∧
      (a15FourSubsetAsFinset s.1 ∩ scratchY1).card = 3 := by
  have hsum := scratch_profile1_sum_formula s.1
  have hcount := scratch_profile1_count_formula s.1
  have heligible :
      a15SubsetSum a15ParityProfile1 s.1 = -60 ∨
        a15SubsetSum a15ParityProfile1 s.1 = 60 := s.2
  have hs' : (15 : Fin 16) ∈ a15FourSubsetAsFinset s.1 := hs
  by_cases h0 : (0 : Fin 16) ∈ a15FourSubsetAsFinset s.1 <;>
    simp only [hs', h0, if_true, if_false] at hsum hcount <;>
    omega

private theorem scratch_profile1_nonanchor_facts
    (s : A15EligibleIndex a15ParityProfile1)
    (hs : ¬a15SubsetContains s 15) :
    a15SubsetSum a15ParityProfile1 s.1 = -60 ∧
      (a15FourSubsetAsFinset s.1 ∩ scratchY1).card = 1 := by
  have hsum := scratch_profile1_sum_formula s.1
  have hcount := scratch_profile1_count_formula s.1
  have heligible :
      a15SubsetSum a15ParityProfile1 s.1 = -60 ∨
        a15SubsetSum a15ParityProfile1 s.1 = 60 := s.2
  have hs' : (15 : Fin 16) ∉ a15FourSubsetAsFinset s.1 := hs
  by_cases h0 : (0 : Fin 16) ∈ a15FourSubsetAsFinset s.1 <;>
    simp only [hs', h0, if_true, if_false] at hsum hcount <;>
    omega

private theorem scratch_profile8_anchor_facts
    (s : A15EligibleIndex a15ParityProfile8)
    (hs : a15SubsetContains s 0) :
    a15SubsetSum a15ParityProfile8 s.1 = -60 ∧
      (a15FourSubsetAsFinset s.1 ∩ scratchY8).card = 3 := by
  have hsum := scratch_profile8_sum_formula s.1
  have hcount := scratch_profile8_count_formula s.1
  have heligible :
      a15SubsetSum a15ParityProfile8 s.1 = -60 ∨
        a15SubsetSum a15ParityProfile8 s.1 = 60 := s.2
  have hs' : (0 : Fin 16) ∈ a15FourSubsetAsFinset s.1 := hs
  by_cases h15 : (15 : Fin 16) ∈ a15FourSubsetAsFinset s.1 <;>
    simp only [hs', h15, if_true, if_false] at hsum hcount <;>
    omega

private theorem scratch_profile8_nonanchor_facts
    (s : A15EligibleIndex a15ParityProfile8)
    (hs : ¬a15SubsetContains s 0) :
    a15SubsetSum a15ParityProfile8 s.1 = 60 ∧
      (a15FourSubsetAsFinset s.1 ∩ scratchY8).card = 1 := by
  have hsum := scratch_profile8_sum_formula s.1
  have hcount := scratch_profile8_count_formula s.1
  have heligible :
      a15SubsetSum a15ParityProfile8 s.1 = -60 ∨
        a15SubsetSum a15ParityProfile8 s.1 = 60 := s.2
  have hs' : (0 : Fin 16) ∉ a15FourSubsetAsFinset s.1 := hs
  by_cases h15 : (15 : Fin 16) ∈ a15FourSubsetAsFinset s.1 <;>
    simp only [hs', h15, if_true, if_false] at hsum hcount <;>
    omega

private theorem scratch_coordinate1_injective :
    Function.Injective a15ParityCoordinate1 := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg Fin.val hij
  simp only [a15ParityCoordinate1] at hval
  omega

private theorem scratch_coordinate8_injective :
    Function.Injective a15ParityCoordinate8 := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg Fin.val hij
  simp only [a15ParityCoordinate8] at hval
  omega

private theorem scratch_support1_image
    (s : A15EligibleIndex a15ParityProfile1) :
    (a15ParitySupport1 s).image a15ParityCoordinate1 =
      a15FourSubsetAsFinset s.1 ∩ scratchY1 := by
  ext i
  constructor
  · intro hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    have hjS :
        a15ParityCoordinate1 j ∈ a15FourSubsetAsFinset s.1 := by
      simpa [a15ParitySupport1] using hj
    exact Finset.mem_inter.mpr
      ⟨hjS, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
  · intro hi
    obtain ⟨hiS, hiY⟩ := Finset.mem_inter.mp hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hiY
    apply Finset.mem_image.mpr
    refine ⟨j, ?_, rfl⟩
    simp [a15ParitySupport1, hiS]

private theorem scratch_support8_image
    (s : A15EligibleIndex a15ParityProfile8) :
    (a15ParitySupport8 s).image a15ParityCoordinate8 =
      a15FourSubsetAsFinset s.1 ∩ scratchY8 := by
  ext i
  constructor
  · intro hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    have hjS :
        a15ParityCoordinate8 j ∈ a15FourSubsetAsFinset s.1 := by
      simpa [a15ParitySupport8] using hj
    exact Finset.mem_inter.mpr
      ⟨hjS, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
  · intro hi
    obtain ⟨hiS, hiY⟩ := Finset.mem_inter.mp hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hiY
    apply Finset.mem_image.mpr
    refine ⟨j, ?_, rfl⟩
    simp [a15ParitySupport8, hiS]

private theorem scratch_support1_card
    (s : A15EligibleIndex a15ParityProfile1)
    (hs : a15SubsetContains s 15) :
    (a15ParitySupport1 s).card = 3 := by
  have himage := congrArg Finset.card (scratch_support1_image s)
  rw [Finset.card_image_of_injective _ scratch_coordinate1_injective] at himage
  rw [himage]
  exact (scratch_profile1_anchor_facts s hs).2

private theorem scratch_support8_card
    (s : A15EligibleIndex a15ParityProfile8)
    (hs : a15SubsetContains s 0) :
    (a15ParitySupport8 s).card = 3 := by
  have himage := congrArg Finset.card (scratch_support8_image s)
  rw [Finset.card_image_of_injective _ scratch_coordinate8_injective] at himage
  rw [himage]
  exact (scratch_profile8_anchor_facts s hs).2

private theorem scratch_shape1
    (s : A15EligibleIndex a15ParityProfile1)
    (hs : a15SubsetContains s 15) :
    a15FourSubsetAsFinset s.1 =
      insert 15 ((a15ParitySupport1 s).image a15ParityCoordinate1) := by
  apply Eq.symm
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hs
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      simpa [a15ParitySupport1] using hj
  · have hcardS : (a15FourSubsetAsFinset s.1).card = 4 := by
      unfold a15FourSubsetAsFinset A15FourSubset.asFinset
      rw [List.toFinset_card_of_nodup
        (a15FourSubsetAt_coordinates_nodup s.1)]
      rfl
    have hanchor :
        (15 : Fin 16) ∉
          (a15ParitySupport1 s).image a15ParityCoordinate1 := by
      intro h
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
      have hval := congrArg Fin.val hj
      simp only [a15ParityCoordinate1] at hval
      omega
    rw [Finset.card_insert_of_notMem hanchor,
      Finset.card_image_of_injective _ scratch_coordinate1_injective,
      scratch_support1_card s hs, hcardS]

private theorem scratch_shape8
    (s : A15EligibleIndex a15ParityProfile8)
    (hs : a15SubsetContains s 0) :
    a15FourSubsetAsFinset s.1 =
      insert 0 ((a15ParitySupport8 s).image a15ParityCoordinate8) := by
  apply Eq.symm
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hs
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      simpa [a15ParitySupport8] using hj
  · have hcardS : (a15FourSubsetAsFinset s.1).card = 4 := by
      unfold a15FourSubsetAsFinset A15FourSubset.asFinset
      rw [List.toFinset_card_of_nodup
        (a15FourSubsetAt_coordinates_nodup s.1)]
      rfl
    have hanchor :
        (0 : Fin 16) ∉
          (a15ParitySupport8 s).image a15ParityCoordinate8 := by
      intro h
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
      have hval := congrArg Fin.val hj
      simp only [a15ParityCoordinate8] at hval
      omega
    rw [Finset.card_insert_of_notMem hanchor,
      Finset.card_image_of_injective _ scratch_coordinate8_injective,
      scratch_support8_card s hs, hcardS]

theorem a15ParitySupport1_card
    (s : A15EligibleIndex a15ParityProfile1)
    (hs : a15SubsetContains s 15) :
    (a15ParitySupport1 s).card = 3 :=
  scratch_support1_card s hs

theorem a15ParitySupport8_card
    (s : A15EligibleIndex a15ParityProfile8)
    (hs : a15SubsetContains s 0) :
    (a15ParitySupport8 s).card = 3 :=
  scratch_support8_card s hs

theorem a15ParityShapeFacts :
    (∀ s : A15EligibleIndex a15ParityProfile1,
        a15SubsetContains s 15 →
          a15FourSubsetAsFinset s.1 =
            insert 15 ((a15ParitySupport1 s).image
              a15ParityCoordinate1)) ∧
    (∀ s : A15EligibleIndex a15ParityProfile8,
        a15SubsetContains s 0 →
          a15FourSubsetAsFinset s.1 =
            insert 0 ((a15ParitySupport8 s).image
              a15ParityCoordinate8)) ∧
    (∀ s : A15EligibleIndex a15ParityProfile1,
        a15SubsetContains s 15 →
          a15SubsetSum a15ParityProfile1 s.1 = 60) ∧
    (∀ s : A15EligibleIndex a15ParityProfile8,
        a15SubsetContains s 0 →
          a15SubsetSum a15ParityProfile8 s.1 = -60) ∧
    (∀ s : A15EligibleIndex a15ParityProfile1,
        ¬a15SubsetContains s 15 →
          a15SubsetSum a15ParityProfile1 s.1 = -60 ∧
          (a15FourSubsetAsFinset s.1 ∩
            Finset.univ.image a15ParityCoordinate1).card = 1) ∧
    (∀ s : A15EligibleIndex a15ParityProfile8,
        ¬a15SubsetContains s 0 →
          a15SubsetSum a15ParityProfile8 s.1 = 60 ∧
          (a15FourSubsetAsFinset s.1 ∩
            Finset.univ.image a15ParityCoordinate8).card = 1) := by
  exact ⟨scratch_shape1, scratch_shape8,
    fun s hs => (scratch_profile1_anchor_facts s hs).1,
    fun s hs => (scratch_profile8_anchor_facts s hs).1,
    scratch_profile1_nonanchor_facts,
    scratch_profile8_nonanchor_facts⟩

def a15ParityTriple1 (s : A15ParityBIndex1) : A15ParityTriple :=
  ⟨a15ParitySupport1 s.1, a15ParitySupport1_card s.1 s.2⟩

def a15ParityTriple8 (s : A15ParityBIndex8) : A15ParityTriple :=
  ⟨a15ParitySupport8 s.1, a15ParitySupport8_card s.1 s.2⟩

private theorem scratch_support1_injective :
    Function.Injective fun s : A15ParityBIndex1 =>
      a15ParitySupport1 s.1 := by
  intro s r h
  apply Subtype.ext
  apply Subtype.ext
  apply a15FourSubsetAsFinset_injective
  change a15ParitySupport1 s.1 = a15ParitySupport1 r.1 at h
  rw [scratch_shape1 s.1 s.2, scratch_shape1 r.1 r.2, h]

private theorem scratch_support8_injective :
    Function.Injective fun s : A15ParityBIndex8 =>
      a15ParitySupport8 s.1 := by
  intro s r h
  apply Subtype.ext
  apply Subtype.ext
  apply a15FourSubsetAsFinset_injective
  change a15ParitySupport8 s.1 = a15ParitySupport8 r.1 at h
  rw [scratch_shape8 s.1 s.2, scratch_shape8 r.1 r.2, h]

private theorem scratch_profile1_sum_of_shape
    (q : A15FourSubsetIndex) (U : Finset (Fin 8))
    (hU : U.card = 3)
    (hq : a15FourSubsetAsFinset q =
      insert 15 (U.image a15ParityCoordinate1)) :
    a15SubsetSum a15ParityProfile1 q = 60 := by
  unfold a15SubsetSum a15DataSubsetSum
  rw [a15FourSubset_valueSum_eq_finset_sum, hq]
  have hanchor :
      (15 : Fin 16) ∉ U.image a15ParityCoordinate1 := by
    intro h
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
    have hval := congrArg Fin.val hj
    simp only [a15ParityCoordinate1] at hval
    omega
  rw [Finset.sum_insert hanchor]
  rw [Finset.sum_image]
  · have hcoord (x : Fin 8) :
        a15ParityProfile1 (a15ParityCoordinate1 x) = 10 := by
      fin_cases x <;> rfl
    simp_rw [hcoord]
    simp [hU]
    decide +kernel
  · exact scratch_coordinate1_injective.injOn

private theorem scratch_profile8_sum_of_shape
    (q : A15FourSubsetIndex) (U : Finset (Fin 8))
    (hU : U.card = 3)
    (hq : a15FourSubsetAsFinset q =
      insert 0 (U.image a15ParityCoordinate8)) :
    a15SubsetSum a15ParityProfile8 q = -60 := by
  unfold a15SubsetSum a15DataSubsetSum
  rw [a15FourSubset_valueSum_eq_finset_sum, hq]
  have hanchor :
      (0 : Fin 16) ∉ U.image a15ParityCoordinate8 := by
    intro h
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
    have hval := congrArg Fin.val hj
    simp only [a15ParityCoordinate8] at hval
    omega
  rw [Finset.sum_insert hanchor]
  rw [Finset.sum_image]
  · have hcoord (x : Fin 8) :
        a15ParityProfile8 (a15ParityCoordinate8 x) = -10 := by
      fin_cases x <;> rfl
    simp_rw [hcoord]
    simp [hU]
    decide +kernel
  · exact scratch_coordinate8_injective.injOn

private theorem scratch_triple1_surjective :
    Function.Surjective a15ParityTriple1 := by
  intro U
  let T : Finset (Fin 16) :=
    insert 15 (U.1.image a15ParityCoordinate1)
  have hanchor :
      (15 : Fin 16) ∉ U.1.image a15ParityCoordinate1 := by
    intro h
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
    have hval := congrArg Fin.val hj
    simp only [a15ParityCoordinate1] at hval
    omega
  have hTcard : T.card = 4 := by
    dsimp only [T]
    rw [Finset.card_insert_of_notMem hanchor,
      Finset.card_image_of_injective _ scratch_coordinate1_injective,
      U.2]
  have hTmem :
      T ∈ (Finset.univ : Finset (Fin 16)).powersetCard 4 := by
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hTcard⟩
  rw [← a15FourSubsetUniverse_complete] at hTmem
  obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hTmem
  have hsum : a15SubsetSum a15ParityProfile1 q = 60 :=
    scratch_profile1_sum_of_shape q U.1 U.2 hq
  let s : A15EligibleIndex a15ParityProfile1 :=
    ⟨q, Or.inr hsum⟩
  have hs : a15SubsetContains s 15 := by
    change (15 : Fin 16) ∈ a15FourSubsetAsFinset q
    rw [hq]
    exact Finset.mem_insert_self 15 _
  let b : A15ParityBIndex1 := ⟨s, hs⟩
  refine ⟨b, ?_⟩
  apply Subtype.ext
  change a15ParitySupport1 s = U.1
  ext j
  simp only [a15ParitySupport1,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hq]
  simp only [T, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro (hanchor' | ⟨k, hk, hkj⟩)
    · have hval := congrArg Fin.val hanchor'
      simp only [a15ParityCoordinate1] at hval
      omega
    · simpa [scratch_coordinate1_injective hkj] using hk
  · intro hj
    exact Or.inr ⟨j, hj, rfl⟩

private theorem scratch_triple8_surjective :
    Function.Surjective a15ParityTriple8 := by
  intro U
  let T : Finset (Fin 16) :=
    insert 0 (U.1.image a15ParityCoordinate8)
  have hanchor :
      (0 : Fin 16) ∉ U.1.image a15ParityCoordinate8 := by
    intro h
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
    have hval := congrArg Fin.val hj
    simp only [a15ParityCoordinate8] at hval
    omega
  have hTcard : T.card = 4 := by
    dsimp only [T]
    rw [Finset.card_insert_of_notMem hanchor,
      Finset.card_image_of_injective _ scratch_coordinate8_injective,
      U.2]
  have hTmem :
      T ∈ (Finset.univ : Finset (Fin 16)).powersetCard 4 := by
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hTcard⟩
  rw [← a15FourSubsetUniverse_complete] at hTmem
  obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hTmem
  have hsum : a15SubsetSum a15ParityProfile8 q = -60 :=
    scratch_profile8_sum_of_shape q U.1 U.2 hq
  let s : A15EligibleIndex a15ParityProfile8 :=
    ⟨q, Or.inl hsum⟩
  have hs : a15SubsetContains s 0 := by
    change (0 : Fin 16) ∈ a15FourSubsetAsFinset q
    rw [hq]
    exact Finset.mem_insert_self 0 _
  let b : A15ParityBIndex8 := ⟨s, hs⟩
  refine ⟨b, ?_⟩
  apply Subtype.ext
  change a15ParitySupport8 s = U.1
  ext j
  simp only [a15ParitySupport8,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hq]
  simp only [T, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro (hanchor' | ⟨k, hk, hkj⟩)
    · have hval := congrArg Fin.val hanchor'
      simp only [a15ParityCoordinate8] at hval
      omega
    · simpa [scratch_coordinate8_injective hkj] using hk
  · intro hj
    exact Or.inr ⟨j, hj, rfl⟩

private theorem a15ParityTriple1_bijective :
    Function.Bijective a15ParityTriple1 := by
  constructor
  · intro s r h
    apply scratch_support1_injective
    exact congrArg Subtype.val h
  · exact scratch_triple1_surjective

private theorem a15ParityTriple8_bijective :
    Function.Bijective a15ParityTriple8 := by
  constructor
  · intro s r h
    apply scratch_support8_injective
    exact congrArg Subtype.val h
  · exact scratch_triple8_surjective

/-- The profile-1 orbit is exactly the 56 triples of an eight-set. -/
noncomputable def a15ParityShellEquiv1 :
    A15ParityTriple ≃ A15ParityBIndex1 :=
  (Equiv.ofBijective a15ParityTriple1
    a15ParityTriple1_bijective).symm

/-- The profile-8 orbit is exactly the same triple universe. -/
noncomputable def a15ParityShellEquiv8 :
    A15ParityTriple ≃ A15ParityBIndex8 :=
  (Equiv.ofBijective a15ParityTriple8
    a15ParityTriple8_bijective).symm

theorem a15ParityCoordinate1_injective :
    Function.Injective a15ParityCoordinate1 :=
  scratch_coordinate1_injective

theorem a15ParityCoordinate8_injective :
    Function.Injective a15ParityCoordinate8 :=
  scratch_coordinate8_injective

end SRG266
