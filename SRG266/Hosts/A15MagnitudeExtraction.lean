/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.A15MagnitudeBasics

/-!
# Extracting the A15 magnitude path from coordinates

For a reduced coordinate list in `[-17,17]`, the multiplicity path is
obtained by counting `-m` and `m` for `m = 17,...,1`.  The canonical list
reconstructed from these counts is proved to be a permutation of the
original list.  Its length, sum, and squared norm are then identified with
the three state quantities used by the recursive enumerator.
-/

namespace SRG266

set_option maxRecDepth 100000
set_option maxHeartbeats 200000

/-- Signed-magnitude choices extracted from a coordinate list. -/
def a15MagnitudeChoicesFrom (coordinates : List ℤ) :
    ℕ → List (ℕ × ℕ)
  | 0 => []
  | m + 1 =>
      (coordinates.count (-((m + 1 : ℕ) : ℤ)),
        coordinates.count ((m + 1 : ℕ) : ℤ)) ::
        a15MagnitudeChoicesFrom coordinates m

@[simp]
theorem a15MagnitudeChoicesFrom_length
    (coordinates : List ℤ) (m : ℕ) :
    (a15MagnitudeChoicesFrom coordinates m).length = m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp [a15MagnitudeChoicesFrom, ih]

theorem a15MagnitudeChoicesFrom_negative_count
    (coordinates : List ℤ) (m : ℕ) (z : ℤ) :
    (a15MagnitudeChoiceNegatives
        (a15MagnitudeChoicesFrom coordinates m)).count z =
      if -(m : ℤ) ≤ z ∧ z ≤ -1 then coordinates.count z else 0 := by
  induction m with
  | zero =>
      simp only [a15MagnitudeChoicesFrom,
        a15MagnitudeChoiceNegatives, List.count_nil]
      split_ifs <;> omega
  | succ m ih =>
      simp only [a15MagnitudeChoicesFrom,
        a15MagnitudeChoiceNegatives, List.count_append,
        List.count_replicate, ih]
      split_ifs <;> simp_all <;> omega

theorem a15MagnitudeChoicesFrom_positive_count
    (coordinates : List ℤ) (m : ℕ) (z : ℤ) :
    (a15MagnitudeChoicePositives
        (a15MagnitudeChoicesFrom coordinates m)).count z =
      if 1 ≤ z ∧ z ≤ m then coordinates.count z else 0 := by
  induction m with
  | zero =>
      simp only [a15MagnitudeChoicesFrom,
        a15MagnitudeChoicePositives, List.count_nil]
      split_ifs <;> omega
  | succ m ih =>
      simp only [a15MagnitudeChoicesFrom,
        a15MagnitudeChoicePositives, List.count_append,
        List.count_replicate, ih]
      split_ifs <;> simp_all <;> omega

/-- Canonical nondecreasing reconstruction from all 17 magnitudes. -/
def a15CanonicalReducedCoordinates (coordinates : List ℤ) : List ℤ :=
  let choices := a15MagnitudeChoicesFrom coordinates 17
  a15MagnitudeChoiceNegatives choices ++
    List.replicate (coordinates.count 0) 0 ++
    a15MagnitudeChoicePositives choices

private theorem a15MagnitudeChoiceNegatives_mem_bounds
    (choices : List (ℕ × ℕ)) {z : ℤ}
    (hz : z ∈ a15MagnitudeChoiceNegatives choices) :
    -(choices.length : ℤ) ≤ z ∧ z ≤ -1 := by
  induction choices with
  | nil => simp [a15MagnitudeChoiceNegatives] at hz
  | cons choice choices ih =>
      rcases choice with ⟨negativeCount, positiveCount⟩
      simp only [a15MagnitudeChoiceNegatives, List.mem_append,
        List.mem_replicate] at hz
      rcases hz with hz | hz
      · rcases hz with ⟨_, rfl⟩
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        omega
      · have h := ih hz
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        omega

private theorem a15MagnitudeChoicePositives_mem_bounds
    (choices : List (ℕ × ℕ)) {z : ℤ}
    (hz : z ∈ a15MagnitudeChoicePositives choices) :
    1 ≤ z ∧ z ≤ choices.length := by
  induction choices with
  | nil => simp [a15MagnitudeChoicePositives] at hz
  | cons choice choices ih =>
      rcases choice with ⟨negativeCount, positiveCount⟩
      simp only [a15MagnitudeChoicePositives, List.mem_append,
        List.mem_replicate] at hz
      rcases hz with hz | hz
      · have h := ih hz
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        omega
      · rcases hz with ⟨_, rfl⟩
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        omega

private theorem a15MagnitudeChoiceNegatives_pairwise
    (choices : List (ℕ × ℕ)) :
    (a15MagnitudeChoiceNegatives choices).Pairwise (· ≤ ·) := by
  induction choices with
  | nil => simp [a15MagnitudeChoiceNegatives]
  | cons choice choices ih =>
      rcases choice with ⟨negativeCount, positiveCount⟩
      rw [a15MagnitudeChoiceNegatives, List.pairwise_append]
      refine ⟨by simp, ih, ?_⟩
      intro a ha b hb
      simp only [List.mem_replicate] at ha
      rcases ha with ⟨_, rfl⟩
      have hbound := a15MagnitudeChoiceNegatives_mem_bounds choices hb
      push_cast
      omega

private theorem a15MagnitudeChoicePositives_pairwise
    (choices : List (ℕ × ℕ)) :
    (a15MagnitudeChoicePositives choices).Pairwise (· ≤ ·) := by
  induction choices with
  | nil => simp [a15MagnitudeChoicePositives]
  | cons choice choices ih =>
      rcases choice with ⟨negativeCount, positiveCount⟩
      rw [a15MagnitudeChoicePositives, List.pairwise_append]
      refine ⟨ih, by simp, ?_⟩
      intro a ha b hb
      simp only [List.mem_replicate] at hb
      rcases hb with ⟨_, rfl⟩
      have hbound := a15MagnitudeChoicePositives_mem_bounds choices ha
      push_cast
      omega

/-- The signed-magnitude reconstruction is genuinely canonical: its entries
are in nondecreasing order. -/
theorem a15CanonicalReducedCoordinates_pairwise
    (coordinates : List ℤ) :
    (a15CanonicalReducedCoordinates coordinates).Pairwise (· ≤ ·) := by
  let choices := a15MagnitudeChoicesFrom coordinates 17
  let negatives := a15MagnitudeChoiceNegatives choices
  let zeros := List.replicate (coordinates.count 0) (0 : ℤ)
  let positives := a15MagnitudeChoicePositives choices
  have hnegative := a15MagnitudeChoiceNegatives_pairwise choices
  have hpositive := a15MagnitudeChoicePositives_pairwise choices
  have hnegZero : ∀ a ∈ negatives, ∀ b ∈ zeros, a ≤ b := by
    intro a ha b hb
    have haBound := a15MagnitudeChoiceNegatives_mem_bounds choices ha
    simp only [zeros, List.mem_replicate] at hb
    rcases hb with ⟨_, rfl⟩
    omega
  have hnegZeroSorted : (negatives ++ zeros).Pairwise (· ≤ ·) := by
    rw [List.pairwise_append]
    exact ⟨hnegative,
      List.pairwise_replicate.mpr (Or.inr (le_refl (0 : ℤ))), hnegZero⟩
  have hleftRight : ∀ a ∈ negatives ++ zeros, ∀ b ∈ positives, a ≤ b := by
    intro a ha b hb
    have hbBound := a15MagnitudeChoicePositives_mem_bounds choices hb
    rcases List.mem_append.mp ha with ha | ha
    · have haBound := a15MagnitudeChoiceNegatives_mem_bounds choices ha
      omega
    · simp only [zeros, List.mem_replicate] at ha
      rcases ha with ⟨_, rfl⟩
      omega
  change (negatives ++ zeros ++ positives).Pairwise (· ≤ ·)
  rw [List.pairwise_append]
  exact ⟨hnegZeroSorted, hpositive, hleftRight⟩

theorem a15CanonicalReducedCoordinates_mem_bounds
    (coordinates : List ℤ) {z : ℤ}
    (hz : z ∈ a15CanonicalReducedCoordinates coordinates) :
    -17 ≤ z ∧ z ≤ 17 := by
  simp only [a15CanonicalReducedCoordinates, List.mem_append,
    List.mem_replicate] at hz
  rcases hz with hz | hz
  · rcases hz with hz | hz
    · have h :=
        a15MagnitudeChoiceNegatives_mem_bounds
          (a15MagnitudeChoicesFrom coordinates 17) hz
      rw [a15MagnitudeChoicesFrom_length coordinates 17] at h
      constructor <;> omega
    · rcases hz with ⟨_, rfl⟩
      omega
  · have h :=
      a15MagnitudeChoicePositives_mem_bounds
        (a15MagnitudeChoicesFrom coordinates 17) hz
    rw [a15MagnitudeChoicesFrom_length coordinates 17] at h
    constructor <;> omega

/-- Counting every value from -17 through 17 reconstructs the original
list up to permutation. -/
theorem a15CanonicalReducedCoordinates_perm
    (coordinates : List ℤ)
    (hbounds : ∀ z ∈ coordinates, -17 ≤ z ∧ z ≤ 17) :
    (a15CanonicalReducedCoordinates coordinates).Perm coordinates := by
  rw [List.perm_iff_count]
  intro z
  simp only [a15CanonicalReducedCoordinates, List.count_append,
    List.count_replicate,
    a15MagnitudeChoicesFrom_negative_count,
    a15MagnitudeChoicesFrom_positive_count]
  by_cases hzZero : z = 0
  · subst z
    simp
  by_cases hzNegative : z < 0
  · have hzUpper : z ≤ -1 := by omega
    have hzZero' : 0 ≠ z := Ne.symm hzZero
    have hzNotPositive : ¬(1 ≤ z ∧ z ≤ (17 : ℤ)) := by omega
    by_cases hzLower : -17 ≤ z
    · simp [hzZero', hzLower, hzUpper, hzNotPositive]
    · have hzCoordinates : z ∉ coordinates := by
        intro hmem
        have := (hbounds z hmem).1
        omega
      rw [List.count_eq_zero.mpr hzCoordinates]
      simp [hzZero', hzLower, hzUpper, hzNotPositive]
  · have hzLower : 1 ≤ z := by omega
    have hzZero' : 0 ≠ z := Ne.symm hzZero
    have hzNotNegative : ¬(-17 ≤ z ∧ z ≤ (-1 : ℤ)) := by omega
    by_cases hzUpper : z ≤ 17
    · simp [hzZero', hzLower, hzUpper, hzNotNegative]
    · have hzCoordinates : z ∉ coordinates := by
        intro hmem
        have := (hbounds z hmem).2
        omega
      rw [List.count_eq_zero.mpr hzCoordinates]
      simp [hzZero', hzLower, hzUpper, hzNotNegative]

theorem a15MagnitudeChoiceNegatives_length_add_positives
    (choices : List (ℕ × ℕ)) :
    (a15MagnitudeChoiceNegatives choices).length +
        (a15MagnitudeChoicePositives choices).length =
      a15MagnitudeChoiceUsed choices := by
  induction choices with
  | nil =>
      simp [a15MagnitudeChoiceNegatives, a15MagnitudeChoicePositives,
        a15MagnitudeChoiceUsed]
  | cons choice choices ih =>
      rcases choice with ⟨negativeCount, positiveCount⟩
      simp only [a15MagnitudeChoiceNegatives,
        a15MagnitudeChoicePositives, a15MagnitudeChoiceUsed,
        List.length_append, List.length_replicate]
      omega

theorem a15CanonicalReducedCoordinates_length
    (coordinates : List ℤ) :
    (a15CanonicalReducedCoordinates coordinates).length =
      a15MagnitudeChoiceUsed (a15MagnitudeChoicesFrom coordinates 17) +
        coordinates.count 0 := by
  unfold a15CanonicalReducedCoordinates
  rw [List.length_append, List.length_append, List.length_replicate]
  have h :=
    a15MagnitudeChoiceNegatives_length_add_positives
      (a15MagnitudeChoicesFrom coordinates 17)
  omega

theorem a15MagnitudeChoice_sum_reconstruction
    (choices : List (ℕ × ℕ)) :
    (a15MagnitudeChoiceNegatives choices).sum +
        (a15MagnitudeChoicePositives choices).sum =
      a15MagnitudeChoiceSum choices := by
  induction choices with
  | nil =>
      simp [a15MagnitudeChoiceNegatives, a15MagnitudeChoicePositives,
        a15MagnitudeChoiceSum]
  | cons choice choices ih =>
      rcases choice with ⟨negativeCount, positiveCount⟩
      simp only [a15MagnitudeChoiceNegatives,
        a15MagnitudeChoicePositives, a15MagnitudeChoiceSum,
        List.sum_append, List.sum_replicate, nsmul_eq_mul]
      push_cast at *
      linear_combination ih

theorem a15CanonicalReducedCoordinates_sum
    (coordinates : List ℤ) :
    (a15CanonicalReducedCoordinates coordinates).sum =
      a15MagnitudeChoiceSum
        (a15MagnitudeChoicesFrom coordinates 17) := by
  unfold a15CanonicalReducedCoordinates
  simp only [List.sum_append, List.sum_replicate, nsmul_eq_mul,
    mul_zero, add_zero]
  simpa only [add_zero] using
    a15MagnitudeChoice_sum_reconstruction
      (a15MagnitudeChoicesFrom coordinates 17)

theorem a15MagnitudeChoice_sq_reconstruction
    (choices : List (ℕ × ℕ)) :
    ((a15MagnitudeChoiceNegatives choices ++
        a15MagnitudeChoicePositives choices).map
          (fun z : ℤ => z * z)).sum =
      a15MagnitudeChoiceSq choices := by
  induction choices with
  | nil =>
      simp [a15MagnitudeChoiceNegatives, a15MagnitudeChoicePositives,
        a15MagnitudeChoiceSq]
  | cons choice choices ih =>
      rcases choice with ⟨negativeCount, positiveCount⟩
      simp only [a15MagnitudeChoiceNegatives,
        a15MagnitudeChoicePositives, a15MagnitudeChoiceSq,
        List.map_append, List.sum_append, List.map_replicate,
        List.sum_replicate, nsmul_eq_mul] at ih ⊢
      push_cast at *
      linear_combination ih

theorem a15CanonicalReducedCoordinates_sq_sum
    (coordinates : List ℤ) :
    ((a15CanonicalReducedCoordinates coordinates).map
        (fun z : ℤ => z * z)).sum =
      a15MagnitudeChoiceSq
        (a15MagnitudeChoicesFrom coordinates 17) := by
  unfold a15CanonicalReducedCoordinates
  simp only [List.map_append, List.sum_append, List.map_replicate,
    List.sum_replicate, nsmul_eq_mul, mul_zero, add_zero]
  simpa only [add_zero, List.map_append, List.sum_append] using
    a15MagnitudeChoice_sq_reconstruction
      (a15MagnitudeChoicesFrom coordinates 17)

end SRG266
