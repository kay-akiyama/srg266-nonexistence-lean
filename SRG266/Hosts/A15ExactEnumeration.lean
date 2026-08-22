/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.A15MagnitudeExtraction
import SRG266.Hosts.A15MagnitudeCompleteness

/-!
# Declarative A15 centroid enumeration

This module mirrors the fast magnitude search but tests the terminal
eligibility threshold by directly computing the cardinality of
`A15EligibleIndex`.  It therefore provides a proof-oriented reference
enumerator independent of the byte pair-sum histogram.

The recursive completeness proof is the same branch argument as for the fast
enumerator.  A separate evaluated theorem compares the two output sets.
-/

namespace SRG266

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Sum of four reduced coordinates in one checked subset record. -/
def a15ReducedDataSubsetSum
    (coordinates : List ℤ) (s : A15FourSubset) : ℤ :=
  coordinates.getD s.a 0 + coordinates.getD s.b 0 +
    coordinates.getD s.c 0 + coordinates.getD s.d 0

/-- Reference eligibility predicate on reduced coordinates. -/
def a15ReducedDataEligible
    (residue : ℤ) (coordinates : List ℤ)
    (s : A15FourSubset) : Bool :=
  let subsetSum := a15ReducedDataSubsetSum coordinates s
  subsetSum = 15 - residue || subsetSum = -15 - residue

/-- Direct count over the checked 1,820-element four-subset universe.

This avoids rebuilding a finite subtype at every one of the 420,403 terminal
norm profiles.  `A15ExactEnumerationSoundness` proves that this optimized
reference count is the cardinality of the declarative eligible subtype. -/
def a15ExactEligibleCardReduced
    (residue : ℤ) (coordinates : List ℤ) : ℕ :=
  a15FourSubsetData.foldl (fun count s =>
    count + if a15ReducedDataEligible residue coordinates s then 1 else 0) 0

/-- Reference recursion using the declarative eligible-shell cardinality at
each complete magnitude profile. -/
def a15ExactEnumerateByMagnitudeAux
    (residue : ℤ) :
    (m remaining : ℕ) → (sum : ℤ) → (sq : ℕ) →
      List ℤ → List ℤ → List (Array ℤ)
  | 0, remaining, sum, sq, negatives, positives =>
      if sum = a15ReducedTargetSum residue &&
          sq = a15ReducedTargetSq residue then
        let reduced :=
          negatives ++ List.replicate remaining 0 ++ positives
        let profile := a15ScaleReducedProfile residue reduced
        if decide (74 ≤
            a15ExactEligibleCardReduced residue reduced) then
          [profile]
        else
          []
      else
        []
  | m + 1, remaining, sum, sq, negatives, positives =>
      (List.range (remaining + 1)).flatMap fun negativeCount =>
        let positiveBound :=
          if residue = 2 && m + 1 = 17 then 0
          else remaining - negativeCount
        (List.range (positiveBound + 1)).flatMap fun positiveCount =>
          let used := negativeCount + positiveCount
          let newRemaining := remaining - used
          let signedMultiplicity : ℤ :=
            (positiveCount : ℤ) - negativeCount
          let newSum := sum + signedMultiplicity * (m + 1)
          let newSq := sq + used * (m + 1) ^ 2
          if a15MagnitudeFeasible residue (m + 1) newRemaining
              newSum newSq then
            a15ExactEnumerateByMagnitudeAux residue m newRemaining
              newSum newSq
              (negatives ++
                List.replicate negativeCount (-((m + 1 : ℕ) : ℤ)))
              (List.replicate positiveCount ((m + 1 : ℕ) : ℤ) ++
                positives)
          else
            []

def a15ExactEnumeratedCandidateProfiles : List (Array ℤ) :=
  a15ExactEnumerateByMagnitudeAux 0 17 16 0 0 [] [] ++
    a15ExactEnumerateByMagnitudeAux 2 17 16 0 0 [] []

/-- Every exact magnitude path is retained by the reference recursion. -/
theorem a15ExactEnumerateByMagnitudeAux_contains_of_choices
    (residue : ℤ) (choices : List (ℕ × ℕ))
    (remaining : ℕ) (sum : ℤ) (sq zeroCount : ℕ)
    (negatives positives : List ℤ)
    (hlength : choices.length ≤ 17)
    (hcount :
      a15MagnitudeChoiceUsed choices + zeroCount = remaining)
    (hsum :
      sum + a15MagnitudeChoiceSum choices =
        a15ReducedTargetSum residue)
    (hsq :
      sq + a15MagnitudeChoiceSq choices =
        a15ReducedTargetSq residue)
    (hspecial :
      residue = 2 → choices.length = 17 →
        choices.head?.map Prod.snd = some 0)
    (heligible :
      74 ≤ a15ExactEligibleCardReduced residue
        (negatives ++ a15MagnitudeChoiceNegatives choices ++
          List.replicate zeroCount 0 ++
          a15MagnitudeChoicePositives choices ++ positives)) :
    a15ScaleReducedProfile residue
        (negatives ++ a15MagnitudeChoiceNegatives choices ++
          List.replicate zeroCount 0 ++
          a15MagnitudeChoicePositives choices ++ positives) ∈
      a15ExactEnumerateByMagnitudeAux residue choices.length remaining
        sum sq negatives positives := by
  induction choices generalizing remaining sum sq negatives positives with
  | nil =>
      simp only [a15MagnitudeChoiceUsed, zero_add] at hcount
      simp only [a15MagnitudeChoiceSum, add_zero] at hsum
      simp only [a15MagnitudeChoiceSq, add_zero] at hsq
      subst remaining
      rw [hsum, hsq]
      simpa [a15ExactEnumerateByMagnitudeAux, heligible,
        a15MagnitudeChoiceNegatives, a15MagnitudeChoicePositives] using
        heligible
  | cons choice choices ih =>
      rcases choice with ⟨negativeCount, positiveCount⟩
      let m := choices.length + 1
      have hlengthSucc : choices.length + 1 ≤ 17 := by
        simpa only [List.length_cons] using hlength
      have hused :
          negativeCount + positiveCount +
              a15MagnitudeChoiceUsed choices + zeroCount =
            remaining := by
        simpa only [a15MagnitudeChoiceUsed, Nat.add_assoc] using hcount
      have hnegative : negativeCount < remaining + 1 := by omega
      have hpositive :
          positiveCount < (remaining - negativeCount) + 1 := by omega
      have htailLength : choices.length ≤ 17 :=
        le_trans (Nat.le_succ choices.length) hlengthSucc
      have htailCount :
          a15MagnitudeChoiceUsed choices + zeroCount =
            remaining - (negativeCount + positiveCount) := by omega
      have htailSum :
          (sum +
              ((positiveCount : ℤ) - negativeCount) * (m : ℤ)) +
              a15MagnitudeChoiceSum choices =
            a15ReducedTargetSum residue := by
        simpa only [a15MagnitudeChoiceSum, m, Nat.cast_add,
          Nat.cast_one, add_assoc] using hsum
      have htailSq :
          (sq + (negativeCount + positiveCount) * m ^ 2) +
              a15MagnitudeChoiceSq choices =
            a15ReducedTargetSq residue := by
        simpa only [a15MagnitudeChoiceSq, m, add_assoc] using hsq
      have hfeasible :
          a15MagnitudeFeasible residue m
            (remaining - (negativeCount + positiveCount))
            (sum +
              ((positiveCount : ℤ) - negativeCount) * (m : ℤ))
            (sq + (negativeCount + positiveCount) * m ^ 2) = true := by
        unfold a15MagnitudeFeasible
        simp only [decide_eq_true_eq]
        have hsqBound := a15MagnitudeChoiceSq_le choices
        have hsumBound := a15MagnitudeChoiceSum_natAbs_le choices
        have hmSub : m - 1 = choices.length := by
          simp [m]
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
            hsqBound.trans
              (Nat.mul_le_mul_right _ husedLe)
          omega
        · rw [hmSub]
          have hdiff :
              a15ReducedTargetSum residue -
                  (sum +
                    ((positiveCount : ℤ) - negativeCount) * (m : ℤ)) =
                a15MagnitudeChoiceSum choices := by
            omega
          rw [hdiff]
          have husedLe :
              a15MagnitudeChoiceUsed choices ≤
                remaining - (negativeCount + positiveCount) := by
            rw [hremainingEq]
            omega
          have hsumRemaining :
              (a15MagnitudeChoiceSum choices).natAbs ≤
                (remaining - (negativeCount + positiveCount)) *
                  choices.length :=
            hsumBound.trans
              (Nat.mul_le_mul_right _ husedLe)
          omega
      have hpositiveBound :
          positiveCount <
            (if residue = 2 && m = 17 then 0
              else remaining - negativeCount) + 1 := by
        by_cases hcase : residue = 2 ∧ m = 17
        · have hhead :
              ((negativeCount, positiveCount) :: choices).head?.map
                  Prod.snd = some 0 := hspecial hcase.1 (by
                    simp only [List.length_cons, m] at hcase ⊢
                    omega)
          simp only [List.head?_cons, Option.map_some] at hhead
          have hp : positiveCount = 0 := by simpa using hhead
          simp [hcase.1, hcase.2, hp]
        · simpa [hcase] using hpositive
      have htailSpecial :
          residue = 2 → choices.length = 17 →
            choices.head?.map Prod.snd = some 0 := by
        intro _ hseventeen
        omega
      have htailEligible :
          74 ≤ a15ExactEligibleCardReduced residue
            ((negatives ++
                List.replicate negativeCount (-((m : ℕ) : ℤ))) ++
                a15MagnitudeChoiceNegatives choices ++
                List.replicate zeroCount 0 ++
                a15MagnitudeChoicePositives choices ++
                (List.replicate positiveCount ((m : ℕ) : ℤ) ++
                  positives)) := by
        simpa only [a15MagnitudeChoiceNegatives,
          a15MagnitudeChoicePositives, m, List.append_assoc] using
          heligible
      have hmemTail :=
        ih (remaining - (negativeCount + positiveCount))
          (sum +
            ((positiveCount : ℤ) - negativeCount) * (m : ℤ))
          (sq + (negativeCount + positiveCount) * m ^ 2)
          (negatives ++
            List.replicate negativeCount (-((m : ℕ) : ℤ)))
          (List.replicate positiveCount ((m : ℕ) : ℤ) ++ positives)
          htailLength htailCount htailSum htailSq htailSpecial
          htailEligible
      have hfeasible' :
          a15MagnitudeFeasible residue (choices.length + 1)
            (remaining - (negativeCount + positiveCount))
            (sum +
              ((positiveCount : ℤ) - negativeCount) *
                ((choices.length : ℤ) + 1))
            (sq + (negativeCount + positiveCount) *
              (choices.length + 1) ^ 2) = true := by
        simpa only [m, Nat.cast_add, Nat.cast_one] using hfeasible
      simp only [List.length_cons, a15ExactEnumerateByMagnitudeAux,
        List.mem_flatMap, a15MagnitudeChoiceNegatives,
        a15MagnitudeChoicePositives]
      refine ⟨negativeCount, List.mem_range.mpr hnegative, ?_⟩
      refine ⟨positiveCount,
        List.mem_range.mpr hpositiveBound, ?_⟩
      simp only [hfeasible', if_true]
      simpa only [m, Nat.cast_add, Nat.cast_one,
        Nat.add_sub_cancel_left, List.append_assoc] using
        hmemTail

/-- A bounded reduced profile satisfying the declarative shell-cardinality
threshold is emitted by the reference enumerator. -/
theorem a15_canonical_reduced_profile_mem_exact_enumeration
    (residue : ℤ) (coordinates : List ℤ)
    (hlength : coordinates.length = 16)
    (hbounds : ∀ z ∈ coordinates, -17 ≤ z ∧ z ≤ 17)
    (hsum : coordinates.sum = a15ReducedTargetSum residue)
    (hsq :
      (coordinates.map (fun z : ℤ => z * z)).sum =
        a15ReducedTargetSq residue)
    (hspecial :
      residue = 2 → coordinates.count 17 = 0)
    (heligible :
      74 ≤ a15ExactEligibleCardReduced residue
        (a15CanonicalReducedCoordinates coordinates)) :
    a15ScaleReducedProfile residue
        (a15CanonicalReducedCoordinates coordinates) ∈
      a15ExactEnumerateByMagnitudeAux residue 17 16 0 0 [] [] := by
  let choices := a15MagnitudeChoicesFrom coordinates 17
  have hchoicesLength : choices.length = 17 := by
    simp [choices]
  have hperm :=
    a15CanonicalReducedCoordinates_perm coordinates hbounds
  have hcanonicalLength :
      (a15CanonicalReducedCoordinates coordinates).length = 16 :=
    hperm.length_eq.trans hlength
  have hcount :
      a15MagnitudeChoiceUsed choices + coordinates.count 0 = 16 := by
    rw [← a15CanonicalReducedCoordinates_length coordinates]
    exact hcanonicalLength
  have hchoiceSum :
      a15MagnitudeChoiceSum choices =
        a15ReducedTargetSum residue := by
    rw [← a15CanonicalReducedCoordinates_sum coordinates]
    exact hperm.sum_eq.trans hsum
  have hsqPerm :
      ((a15CanonicalReducedCoordinates coordinates).map
          (fun z : ℤ => z * z)).sum =
        (coordinates.map (fun z : ℤ => z * z)).sum :=
    (hperm.map (fun z : ℤ => z * z)).sum_eq
  have hchoiceSq :
      a15MagnitudeChoiceSq choices =
        a15ReducedTargetSq residue := by
    have hchoiceSqInt :
        (a15MagnitudeChoiceSq choices : ℤ) =
          a15ReducedTargetSq residue := by
      rw [← a15CanonicalReducedCoordinates_sq_sum coordinates,
        hsqPerm]
      exact hsq
    exact_mod_cast hchoiceSqInt
  have hchoiceSpecial :
      residue = 2 → choices.length = 17 →
        choices.head?.map Prod.snd = some 0 := by
    intro hresidue _
    simp only [choices, a15MagnitudeChoicesFrom, List.head?_cons,
      Option.map_some]
    exact congrArg some (hspecial hresidue)
  have heligibleChoices :
      74 ≤ a15ExactEligibleCardReduced residue
        ([] ++ a15MagnitudeChoiceNegatives choices ++
          List.replicate (coordinates.count 0) 0 ++
          a15MagnitudeChoicePositives choices ++ []) := by
    simpa only [a15CanonicalReducedCoordinates, choices,
      List.nil_append, List.append_nil] using heligible
  have hmem :=
    a15ExactEnumerateByMagnitudeAux_contains_of_choices residue choices
      16 0 0 (coordinates.count 0) [] []
      (by omega) hcount (by simpa using hchoiceSum)
      (by simpa using hchoiceSq) hchoiceSpecial
      heligibleChoices
  rw [hchoicesLength] at hmem
  simpa only [a15CanonicalReducedCoordinates, choices,
    List.nil_append, List.append_nil] using hmem

end SRG266
