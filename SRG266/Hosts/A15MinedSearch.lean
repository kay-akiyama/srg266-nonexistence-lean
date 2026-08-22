/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.A15MagnitudeExtraction
import SRG266.Hosts.A15MinedNormSearch

/-!
# The mined small A15 centroid search

The local-design congruence makes every coordinate of the scaled `A₁₅⁺`
centroid divisible by ten.  After division, the norm-4800 search becomes
the classification of sixteen integers with sum zero, squared norm 48, and a
common parity.  This module implements that six-magnitude search directly.

It has only 17 norm profiles.  The shell-cardinality threshold removes two of
them, leaving 15 profiles before the final Farkas/projector reduction.
-/

namespace SRG266

set_option maxRecDepth 100000

theorem a15SmallCommonParity_of_mod_eq
    (coordinates : List ℤ) (p : ℤ)
    (hall : ∀ z ∈ coordinates, z % 2 = p)
    (hzero : coordinates.getD 0 0 % 2 = p) :
    a15SmallCommonParity coordinates = true := by
  unfold a15SmallCommonParity
  apply List.all_eq_true.mpr
  intro z hz
  simpa only [decide_eq_true_eq, hall z hz] using hzero.symm

/-- Canonical nondecreasing reconstruction using only magnitudes at most six. -/
def a15SmallCanonicalCoordinates (coordinates : List ℤ) : List ℤ :=
  let choices := a15MagnitudeChoicesFrom coordinates 6
  a15MagnitudeChoiceNegatives choices ++
    List.replicate (coordinates.count 0) 0 ++
    a15MagnitudeChoicePositives choices

/-- Sum of a checked four-subset in divided centroid coordinates. -/
def a15SmallFourSubsetSum
    (coordinates : List ℤ) (s : A15FourSubset) : ℤ :=
  coordinates.getD s.a 0 + coordinates.getD s.b 0 +
    coordinates.getD s.c 0 + coordinates.getD s.d 0

/-- The scaled subset-sum condition `±60`, divided by ten. -/
def a15SmallDataEligible
    (coordinates : List ℤ) (s : A15FourSubset) : Bool :=
  let subsetSum := a15SmallFourSubsetSum coordinates s
  subsetSum = 6 || subsetSum = -6

/-- Recover the scaled centroid profile by multiplying the divided coordinates
by ten. -/
def a15SmallProfile (coordinates : List ℤ) : Fin 16 → ℤ :=
  fun i => 10 * coordinates.getD i.1 0

/-- Direct eligible-shell count on a small profile. -/
def a15SmallEligibleCount (coordinates : List ℤ) : ℕ :=
  a15EligibleCount (a15SmallProfile coordinates)

/-! ## Completeness of the six-magnitude recursion -/

/-- Every exact small magnitude path survives the sound pruning tests. -/
theorem a15SmallEnumerateByMagnitudeAux_contains_of_choices
    (choices : List (ℕ × ℕ))
    (remaining : ℕ) (sum : ℤ) (sq zeroCount : ℕ)
    (negatives positives : List ℤ)
    (hcount :
      a15MagnitudeChoiceUsed choices + zeroCount = remaining)
    (hsum : sum + a15MagnitudeChoiceSum choices = 0)
    (hsq : sq + a15MagnitudeChoiceSq choices = 48)
    (hparity :
      a15SmallCommonParity
        (negatives ++ a15MagnitudeChoiceNegatives choices ++
          List.replicate zeroCount 0 ++
          a15MagnitudeChoicePositives choices ++ positives) = true) :
    negatives ++ a15MagnitudeChoiceNegatives choices ++
        List.replicate zeroCount 0 ++
        a15MagnitudeChoicePositives choices ++ positives ∈
      a15SmallEnumerateByMagnitudeAux choices.length remaining
        sum sq negatives positives := by
  induction choices generalizing remaining sum sq negatives positives with
  | nil =>
      simp only [a15MagnitudeChoiceUsed, zero_add] at hcount
      simp only [a15MagnitudeChoiceSum, add_zero] at hsum
      simp only [a15MagnitudeChoiceSq, add_zero] at hsq
      subst remaining
      rw [hsum, hsq]
      simpa [a15SmallEnumerateByMagnitudeAux, hparity,
        a15MagnitudeChoiceNegatives, a15MagnitudeChoicePositives] using hparity
  | cons choice choices ih =>
      rcases choice with ⟨negativeCount, positiveCount⟩
      let m := choices.length + 1
      have hused :
          negativeCount + positiveCount +
              a15MagnitudeChoiceUsed choices + zeroCount =
            remaining := by
        simpa only [a15MagnitudeChoiceUsed, Nat.add_assoc] using hcount
      have hnegative : negativeCount < remaining + 1 := by omega
      have hpositive :
          positiveCount < remaining - negativeCount + 1 := by omega
      have htailCount :
          a15MagnitudeChoiceUsed choices + zeroCount =
            remaining - (negativeCount + positiveCount) := by omega
      have htailSum :
          (sum +
              ((positiveCount : ℤ) - negativeCount) * (m : ℤ)) +
              a15MagnitudeChoiceSum choices = 0 := by
        simpa only [a15MagnitudeChoiceSum, m, Nat.cast_add,
          Nat.cast_one, add_assoc] using hsum
      have htailSq :
          (sq + (negativeCount + positiveCount) * m ^ 2) +
              a15MagnitudeChoiceSq choices = 48 := by
        simpa only [a15MagnitudeChoiceSq, m, add_assoc] using hsq
      have hfeasible :
          a15SmallMagnitudeFeasible m
            (remaining - (negativeCount + positiveCount))
            (sum +
              ((positiveCount : ℤ) - negativeCount) * (m : ℤ))
            (sq + (negativeCount + positiveCount) * m ^ 2) = true := by
        unfold a15SmallMagnitudeFeasible
        simp only [decide_eq_true_eq]
        have hsqBound := a15MagnitudeChoiceSq_le choices
        have hsumBound := a15MagnitudeChoiceSum_natAbs_le choices
        have hmSub : m - 1 = choices.length := by simp [m]
        have hremainingEq :
            remaining - (negativeCount + positiveCount) =
              a15MagnitudeChoiceUsed choices + zeroCount :=
          htailCount.symm
        constructor
        · omega
        constructor
        · rw [hmSub]
          have husedLe :
              a15MagnitudeChoiceUsed choices ≤
                remaining - (negativeCount + positiveCount) := by
            rw [hremainingEq]
            omega
          have hsqRemaining :
              a15MagnitudeChoiceSq choices ≤
                (remaining - (negativeCount + positiveCount)) *
                  choices.length ^ 2 :=
            hsqBound.trans (Nat.mul_le_mul_right _ husedLe)
          omega
        · rw [hmSub]
          have hdiff :
              sum +
                  ((positiveCount : ℤ) - negativeCount) * (m : ℤ) =
                -a15MagnitudeChoiceSum choices := by
            omega
          rw [hdiff, Int.natAbs_neg]
          have husedLe :
              a15MagnitudeChoiceUsed choices ≤
                remaining - (negativeCount + positiveCount) := by
            rw [hremainingEq]
            omega
          exact hsumBound.trans (Nat.mul_le_mul_right _ husedLe)
      have htailParity :
          a15SmallCommonParity
            ((negatives ++
                List.replicate negativeCount (-((m : ℕ) : ℤ))) ++
                a15MagnitudeChoiceNegatives choices ++
                List.replicate zeroCount 0 ++
                a15MagnitudeChoicePositives choices ++
                (List.replicate positiveCount ((m : ℕ) : ℤ) ++ positives)) =
              true := by
        simpa only [a15MagnitudeChoiceNegatives,
          a15MagnitudeChoicePositives, m, List.append_assoc] using hparity
      have hmemTail :=
        ih (remaining - (negativeCount + positiveCount))
          (sum +
            ((positiveCount : ℤ) - negativeCount) * (m : ℤ))
          (sq + (negativeCount + positiveCount) * m ^ 2)
          (negatives ++
            List.replicate negativeCount (-((m : ℕ) : ℤ)))
          (List.replicate positiveCount ((m : ℕ) : ℤ) ++ positives)
          htailCount htailSum htailSq htailParity
      have hfeasible' :
          a15SmallMagnitudeFeasible (choices.length + 1)
            (remaining - (negativeCount + positiveCount))
            (sum +
              ((positiveCount : ℤ) - negativeCount) *
                ((choices.length : ℤ) + 1))
            (sq + (negativeCount + positiveCount) *
              (choices.length + 1) ^ 2) = true := by
        simpa only [m, Nat.cast_add, Nat.cast_one] using hfeasible
      simp only [List.length_cons, a15SmallEnumerateByMagnitudeAux,
        List.mem_flatMap, a15MagnitudeChoiceNegatives,
        a15MagnitudeChoicePositives]
      refine ⟨negativeCount, List.mem_range.mpr hnegative, ?_⟩
      refine ⟨positiveCount, List.mem_range.mpr hpositive, ?_⟩
      simp only [hfeasible', if_true]
      simpa only [m, Nat.cast_add, Nat.cast_one,
        Nat.add_sub_cancel_left, List.append_assoc] using hmemTail

/-- Counting the values from `-6` through `6` reconstructs a bounded list up
to permutation. -/
theorem a15SmallCanonicalCoordinates_perm
    (coordinates : List ℤ)
    (hbounds : ∀ z ∈ coordinates, -6 ≤ z ∧ z ≤ 6) :
    (a15SmallCanonicalCoordinates coordinates).Perm coordinates := by
  rw [List.perm_iff_count]
  intro z
  simp only [a15SmallCanonicalCoordinates, List.count_append,
    List.count_replicate,
    a15MagnitudeChoicesFrom_negative_count,
    a15MagnitudeChoicesFrom_positive_count]
  by_cases hzZero : z = 0
  · subst z
    simp
  by_cases hzNegative : z < 0
  · have hzUpper : z ≤ -1 := by omega
    have hzZero' : 0 ≠ z := Ne.symm hzZero
    have hzNotPositive : ¬(1 ≤ z ∧ z ≤ (6 : ℤ)) := by omega
    by_cases hzLower : -6 ≤ z
    · simp [hzZero', hzLower, hzUpper, hzNotPositive]
    · have hzCoordinates : z ∉ coordinates := by
        intro hmem
        have := (hbounds z hmem).1
        omega
      rw [List.count_eq_zero.mpr hzCoordinates]
      simp [hzZero', hzLower, hzUpper, hzNotPositive]
  · have hzLower : 1 ≤ z := by omega
    have hzZero' : 0 ≠ z := Ne.symm hzZero
    have hzNotNegative : ¬(-6 ≤ z ∧ z ≤ (-1 : ℤ)) := by omega
    by_cases hzUpper : z ≤ 6
    · simp [hzZero', hzLower, hzUpper, hzNotNegative]
    · have hzCoordinates : z ∉ coordinates := by
        intro hmem
        have := (hbounds z hmem).2
        omega
      rw [List.count_eq_zero.mpr hzCoordinates]
      simp [hzZero', hzLower, hzUpper, hzNotNegative]

theorem a15SmallCanonicalCoordinates_length (coordinates : List ℤ) :
    (a15SmallCanonicalCoordinates coordinates).length =
      a15MagnitudeChoiceUsed (a15MagnitudeChoicesFrom coordinates 6) +
        coordinates.count 0 := by
  unfold a15SmallCanonicalCoordinates
  rw [List.length_append, List.length_append, List.length_replicate]
  have h :=
    a15MagnitudeChoiceNegatives_length_add_positives
      (a15MagnitudeChoicesFrom coordinates 6)
  omega

theorem a15SmallCanonicalCoordinates_sum (coordinates : List ℤ) :
    (a15SmallCanonicalCoordinates coordinates).sum =
      a15MagnitudeChoiceSum (a15MagnitudeChoicesFrom coordinates 6) := by
  unfold a15SmallCanonicalCoordinates
  simp only [List.sum_append, List.sum_replicate, nsmul_eq_mul,
    mul_zero, add_zero]
  simpa only [add_zero] using
    a15MagnitudeChoice_sum_reconstruction
      (a15MagnitudeChoicesFrom coordinates 6)

theorem a15SmallCanonicalCoordinates_sq_sum (coordinates : List ℤ) :
    ((a15SmallCanonicalCoordinates coordinates).map
        (fun z : ℤ => z * z)).sum =
      a15MagnitudeChoiceSq (a15MagnitudeChoicesFrom coordinates 6) := by
  unfold a15SmallCanonicalCoordinates
  simp only [List.map_append, List.sum_append, List.map_replicate,
    List.sum_replicate, nsmul_eq_mul, mul_zero, add_zero]
  simpa only [add_zero, List.map_append, List.sum_append] using
    a15MagnitudeChoice_sq_reconstruction
      (a15MagnitudeChoicesFrom coordinates 6)

/-- Every bounded profile with the mined invariants follows a branch of the
small recursion. -/
theorem a15SmallCanonicalCoordinates_mem_normProfiles
    (coordinates : List ℤ)
    (hlength : coordinates.length = 16)
    (hbounds : ∀ z ∈ coordinates, -6 ≤ z ∧ z ≤ 6)
    (hsum : coordinates.sum = 0)
    (hsq : (coordinates.map (fun z : ℤ => z * z)).sum = 48)
    (hparity :
      a15SmallCommonParity (a15SmallCanonicalCoordinates coordinates) = true) :
    a15SmallCanonicalCoordinates coordinates ∈ a15SmallNormProfiles := by
  let choices := a15MagnitudeChoicesFrom coordinates 6
  have hchoicesLength : choices.length = 6 := by simp [choices]
  have hperm := a15SmallCanonicalCoordinates_perm coordinates hbounds
  have hcanonicalLength :
      (a15SmallCanonicalCoordinates coordinates).length = 16 :=
    hperm.length_eq.trans hlength
  have hcount :
      a15MagnitudeChoiceUsed choices + coordinates.count 0 = 16 := by
    rw [← a15SmallCanonicalCoordinates_length coordinates]
    exact hcanonicalLength
  have hchoiceSum : a15MagnitudeChoiceSum choices = 0 := by
    rw [← a15SmallCanonicalCoordinates_sum coordinates]
    exact hperm.sum_eq.trans hsum
  have hsqPerm :
      ((a15SmallCanonicalCoordinates coordinates).map
          (fun z : ℤ => z * z)).sum =
        (coordinates.map (fun z : ℤ => z * z)).sum :=
    (hperm.map (fun z : ℤ => z * z)).sum_eq
  have hchoiceSq : a15MagnitudeChoiceSq choices = 48 := by
    have hchoiceSqInt : (a15MagnitudeChoiceSq choices : ℤ) = 48 := by
      rw [← a15SmallCanonicalCoordinates_sq_sum coordinates, hsqPerm]
      exact hsq
    exact_mod_cast hchoiceSqInt
  have hmem :=
    a15SmallEnumerateByMagnitudeAux_contains_of_choices choices
      16 0 0 (coordinates.count 0) [] [] hcount
      (by simpa using hchoiceSum) (by simpa using hchoiceSq)
      (by simpa only [a15SmallCanonicalCoordinates, choices,
        List.nil_append, List.append_nil] using hparity)
  rw [hchoicesLength] at hmem
  simpa only [a15SmallNormProfiles, a15SmallCanonicalCoordinates, choices,
    List.nil_append, List.append_nil] using hmem

end SRG266
