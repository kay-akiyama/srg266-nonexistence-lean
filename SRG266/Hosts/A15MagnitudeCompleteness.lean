/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.A15EnumerationPrerequisites
import SRG266.Hosts.A15MagnitudeBasics

/-!
# Completeness of the A15 magnitude-search recursion

The native A15 search chooses, from magnitude 17 down to one, the
multiplicities of the negative and positive reduced coordinates.  This file
proves that every exact list of such choices follows a branch of the search.
In particular, all three pruning inequalities are shown to be necessary:
the remaining coordinates bound their own squared norm and signed sum.

This is a structural theorem about the recursive generator.  Constructing
the choice list from an arbitrary canonical centroid is handled separately.
-/

namespace SRG266

set_option maxRecDepth 100000

/-- Every exact magnitude path is retained by the recursive A15 generator.

The special condition at length 17 expresses the coordinate bound for
residue two: reduced coordinate `+17` would scale to 70 and is therefore
forbidden. -/
theorem a15EnumerateByMagnitudeAux_contains_of_choices
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
      74 ≤ a15FastEligibleCountReduced residue
        (negatives ++ a15MagnitudeChoiceNegatives choices ++
          List.replicate zeroCount 0 ++
          a15MagnitudeChoicePositives choices ++ positives)) :
    a15ScaleReducedProfile residue
        (negatives ++ a15MagnitudeChoiceNegatives choices ++
          List.replicate zeroCount 0 ++
          a15MagnitudeChoicePositives choices ++ positives) ∈
      a15EnumerateByMagnitudeAux residue choices.length remaining
        sum sq negatives positives := by
  induction choices generalizing remaining sum sq negatives positives with
  | nil =>
      simp only [a15MagnitudeChoiceUsed, zero_add] at hcount
      simp only [a15MagnitudeChoiceSum, add_zero] at hsum
      simp only [a15MagnitudeChoiceSq, add_zero] at hsq
      subst remaining
      rw [hsum, hsq]
      simpa [a15EnumerateByMagnitudeAux, heligible,
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
        have : choices.length + 1 ≤ 17 := hlengthSucc
        omega
      have htailEligible :
          74 ≤ a15FastEligibleCountReduced residue
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
      simp only [List.length_cons, a15EnumerateByMagnitudeAux,
        List.mem_flatMap, a15MagnitudeChoiceNegatives,
        a15MagnitudeChoicePositives]
      refine ⟨negativeCount, List.mem_range.mpr hnegative, ?_⟩
      refine ⟨positiveCount,
        List.mem_range.mpr hpositiveBound, ?_⟩
      simp only [hfeasible', if_true]
      simpa only [m, Nat.cast_add, Nat.cast_one,
        Nat.add_sub_cancel_left, List.append_assoc] using
        hmemTail

end SRG266
