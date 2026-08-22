/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.A15ProjectorBridge

/-!
# Structural standard-difference moments for the `A₁₅⁺` shell

The shell coordinates are, up to a global sign, `-3` on a four-subset and
`1` off it.  This module proves directly that the ordered squared-difference
moment inside a coordinate class of size `n`, containing `r` selected
coordinates, is `32 r (n-r)`.  No shell enumeration is needed.
-/

open scoped BigOperators

namespace SRG266

theorem a15_sum_sq_sub
    {α : Type*} [DecidableEq α]
    (C : Finset α) (z : α → ℤ) :
    (∑ i ∈ C, ∑ j ∈ C.erase i, (z i - z j) ^ 2) =
      2 * (C.card : ℤ) * (∑ i ∈ C, z i ^ 2) -
        2 * (∑ i ∈ C, z i) ^ 2 := by
  have herase (i : α) (hi : i ∈ C) :
      (∑ j ∈ C.erase i, (z i - z j) ^ 2) =
        ∑ j ∈ C, (z i - z j) ^ 2 := by
    rw [← Finset.sum_erase_add _ _ hi]
    ring
  have hcross :
      (∑ i ∈ C, ∑ j ∈ C, z i * z j) =
        (∑ i ∈ C, z i) ^ 2 := by
    rw [sq, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
  have hdiag :
      (∑ i ∈ C, (C.card : ℤ) * z i ^ 2) =
        (C.card : ℤ) * ∑ i ∈ C, z i ^ 2 := by
    rw [Finset.mul_sum]
  have hdiagTwo :
      (∑ i ∈ C, 2 * (C.card : ℤ) * z i ^ 2) =
        2 * (C.card : ℤ) * ∑ i ∈ C, z i ^ 2 := by
    rw [Finset.mul_sum]
  have hcrossTwo :
      (∑ i ∈ C, ∑ j ∈ C, 2 * z i * z j) =
        2 * (∑ i ∈ C, z i) ^ 2 := by
    calc
      _ = 2 * (∑ i ∈ C, ∑ j ∈ C, z i * z j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by rw [hcross]
  have hpoint (i j : α) :
      (z i - z j) ^ 2 = z i ^ 2 - 2 * z i * z j + z j ^ 2 := by
    ring
  calc
    _ = ∑ i ∈ C, ∑ j ∈ C, (z i - z j) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact herase i hi
    _ = _ := by
      simp_rw [hpoint]
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
      rw [hdiag, hdiagTwo, hcrossTwo]
      ring

def a15SignedCoordinate {α : Type*} [DecidableEq α]
    (S : Finset α) (i : α) : ℤ :=
  if i ∈ S then -3 else 1

theorem a15_signed_sum
    {α : Type*} [DecidableEq α] (C S : Finset α) :
    (∑ i ∈ C, a15SignedCoordinate S i) =
      (C.card : ℤ) - 4 * ((C ∩ S).card : ℤ) := by
  simp only [a15SignedCoordinate]
  have hpoint (i : α) :
      (if i ∈ S then (-3 : ℤ) else 1) =
        1 - 4 * if i ∈ S then 1 else 0 := by
    by_cases hi : i ∈ S <;> simp [hi]
  simp_rw [hpoint, Finset.sum_sub_distrib]
  simp
  ring

theorem a15_signed_sq_sum
    {α : Type*} [DecidableEq α] (C S : Finset α) :
    (∑ i ∈ C, a15SignedCoordinate S i ^ 2) =
      (C.card : ℤ) + 8 * ((C ∩ S).card : ℤ) := by
  simp only [a15SignedCoordinate]
  have hpoint (i : α) :
      (if i ∈ S then (-3 : ℤ) else 1) ^ 2 =
        1 + 8 * if i ∈ S then 1 else 0 := by
    by_cases hi : i ∈ S <;> simp [hi]
  simp_rw [hpoint, Finset.sum_add_distrib]
  simp
  ring

theorem a15_signed_difference_moment
    {α : Type*} [DecidableEq α] (C S : Finset α) :
    (∑ i ∈ C, ∑ j ∈ C.erase i,
        (a15SignedCoordinate S i - a15SignedCoordinate S j) ^ 2) =
      32 * ((C ∩ S).card : ℤ) *
        ((C.card : ℤ) - (C ∩ S).card) := by
  rw [a15_sum_sq_sub, a15_signed_sum, a15_signed_sq_sum]
  ring

theorem a15ProjectorClassCount_eq_card
    (profile : A15ProjectorProfile) (c : ℕ)
    (s : A15FourSubsetIndex) :
    a15ProjectorClassCount profile.classSizes (a15FourSubsetAt s) c =
      (profile.classFinset c ∩ a15FourSubsetAsFinset s).card := by
  have hincreasing := a15FourSubsetAt_increasing s
  rcases hincreasing with ⟨hab, hbc, hcd, hd⟩
  have hraw :
      a15ProjectorRawCoordinates (a15FourSubsetAt s) =
        (a15FourSubsetAt s).coordinates.map Fin.val := by
    simp only [a15ProjectorRawCoordinates, A15FourSubset.coordinates,
      List.map_cons, List.map_nil, a15FourSubsetCoordinate]
    simp only [Nat.mod_eq_of_lt (by omega : (a15FourSubsetAt s).a < 16),
      Nat.mod_eq_of_lt (by omega : (a15FourSubsetAt s).b < 16),
      Nat.mod_eq_of_lt (by omega : (a15FourSubsetAt s).c < 16),
      Nat.mod_eq_of_lt hd]
  let p : Fin 16 → Bool := fun i => decide (profile.inClass c i)
  have hfin :
      profile.classFinset c ∩ a15FourSubsetAsFinset s =
        ((a15FourSubsetAt s).coordinates.filter p).toFinset := by
    ext i
    simp [A15ProjectorProfile.classFinset, a15FourSubsetAsFinset,
      A15FourSubset.asFinset, p, and_comm]
  rw [hfin, List.toFinset_card_of_nodup
    ((a15FourSubsetAt_coordinates_nodup s).filter p)]
  rw [← List.countP_eq_length_filter]
  unfold a15ProjectorClassCount
  rw [hraw]
  simp only [List.countP_map]
  apply List.countP_congr
  intro i hi
  simp [p, A15ProjectorProfile.inClass]

theorem a15_shell_difference_sq
    (profile : A15ProjectorProfile)
    (s : A15EligibleIndex profile.centroidVector) (i j : Fin 16) :
    (a15ProjectorShellCoordinate profile.d (a15FourSubsetAt s.1) i -
        a15ProjectorShellCoordinate profile.d (a15FourSubsetAt s.1) j) ^ 2 =
      (a15SignedCoordinate (a15FourSubsetAsFinset s.1) i -
        a15SignedCoordinate (a15FourSubsetAsFinset s.1) j) ^ 2 := by
  rw [a15ProjectorShellCoordinate_eq_shellVector4 profile s i,
    a15ProjectorShellCoordinate_eq_shellVector4 profile s j]
  unfold a15ShellVector4 a15ShellCoordinate4 a15SignedCoordinate
  by_cases hsum : a15SubsetSum profile.centroidVector s.1 = 60 <;>
    by_cases hi : i ∈ a15FourSubsetAsFinset s.1 <;>
      by_cases hj : j ∈ a15FourSubsetAsFinset s.1 <;>
        simp [hsum, hi, hj]

def A15ProjectorProfile.shellDifferenceMoment
    (profile : A15ProjectorProfile) (c : ℕ)
    (s : A15EligibleIndex profile.centroidVector) : ℤ :=
  ∑ i ∈ profile.classFinset c,
    ∑ j ∈ (profile.classFinset c).erase i,
      (a15ProjectorShellCoordinate profile.d (a15FourSubsetAt s.1) i -
        a15ProjectorShellCoordinate profile.d (a15FourSubsetAt s.1) j) ^ 2

theorem A15ProjectorProfile.shellDifferenceMoment_eq_card
    (profile : A15ProjectorProfile) (c : ℕ)
    (s : A15EligibleIndex profile.centroidVector) :
    A15ProjectorProfile.shellDifferenceMoment profile c s =
      32 * ((profile.classFinset c ∩ a15FourSubsetAsFinset s.1).card : ℤ) *
        (((profile.classFinset c).card : ℤ) -
          ((profile.classFinset c ∩ a15FourSubsetAsFinset s.1).card : ℤ)) := by
  unfold A15ProjectorProfile.shellDifferenceMoment
  calc
    _ = ∑ i ∈ profile.classFinset c,
        ∑ j ∈ (profile.classFinset c).erase i,
          (a15SignedCoordinate (a15FourSubsetAsFinset s.1) i -
            a15SignedCoordinate (a15FourSubsetAsFinset s.1) j) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact a15_shell_difference_sq profile s i j
    _ = _ := a15_signed_difference_moment
      (profile.classFinset c) (a15FourSubsetAsFinset s.1)

theorem A15ProjectorProfile.indexMatches_classCount
    (profile : A15ProjectorProfile)
    (k : Fin profile.orbits.size) (c : Fin profile.classSizes.size)
    (s : A15FourSubsetIndex) (hmatch : profile.indexMatches k.1 s) :
    profile.orbitClassCount k.1 c.1 =
      a15ProjectorClassCount profile.classSizes (a15FourSubsetAt s) c.1 := by
  unfold A15ProjectorProfile.indexMatches A15ProjectorOrbit.matches at hmatch
  simp only [Bool.and_eq_true] at hmatch
  have hall := List.all_eq_true.mp hmatch.2
  have hc := hall c.1 (List.mem_range.mpr c.isLt)
  have heq := of_decide_eq_true hc
  unfold A15ProjectorProfile.orbitClassCount
  simpa [Array.getD, k.isLt] using heq

def A15ProjectorProfile.standardAverageValid (profile : A15ProjectorProfile) : Prop :=
  ∀ k : Fin profile.orbits.size,
    ∀ c : Fin profile.classSizes.size,
      ∀ s : A15EligibleIndex profile.centroidVector,
        profile.indexMatches k.1 s.1 →
          A15ProjectorProfile.shellDifferenceMoment profile c.1 s =
            32 * (profile.orbitClassCount k.1 c.1 : ℤ) *
              ((profile.classSizes.getD c.1 0 : ℤ) -
                profile.orbitClassCount k.1 c.1)

instance (profile : A15ProjectorProfile) :
    Decidable profile.standardAverageValid := by
  unfold A15ProjectorProfile.standardAverageValid
  infer_instance

theorem A15ProjectorProfile.standardAverageValid_of_bridgeValid
    (profile : A15ProjectorProfile) (hbridge : profile.bridgeValid) :
    A15ProjectorProfile.standardAverageValid profile := by
  rcases hbridge with
    ⟨_, _, _, _, _, hclasses, _, _, _⟩
  intro k c s hmatch
  rw [A15ProjectorProfile.shellDifferenceMoment_eq_card]
  have hcount :
      ((profile.classFinset c.1 ∩
          a15FourSubsetAsFinset s.1).card : ℤ) =
        profile.orbitClassCount k.1 c.1 := by
    norm_cast
    exact (a15ProjectorClassCount_eq_card profile c.1 s.1).symm.trans
      (A15ProjectorProfile.indexMatches_classCount profile k c s.1 hmatch).symm
  have hclass :
      ((profile.classFinset c.1).card : ℤ) =
        profile.classSizes.getD c.1 0 := by
    norm_cast
    exact (hclasses c).2.1
  rw [hcount, hclass]

end SRG266
