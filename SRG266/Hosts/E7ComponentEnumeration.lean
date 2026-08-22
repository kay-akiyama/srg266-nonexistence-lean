/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.E7ComponentEnumerationCore
import SRG266.Hosts.A15MagnitudeExtraction

/-!
# Native enumeration of canonical E7 component profiles

A doubled E7 coordinate vector has eight coordinates of one parity, sum
zero, and squared norm at most 1200.  Writing `yᵢ = 2aᵢ + p` gives two
reduced searches:

* `p = 0`: `sum a = 0` and `sum a² ≤ 300`;
* `p = 1`: `sum a = -4` and `sum a² ≤ 302`.

The generator uses signed absolute-value multiplicities from magnitude 17
down to one.  The same structural path representation used for A15 makes
the pruning-completeness proof short and independent of the native
evaluation.
-/

namespace SRG266

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Every exact signed-magnitude path satisfying the component invariants is
retained by the generator. -/
theorem e7EnumerateComponentsByMagnitudeAux_contains_of_choices
    (parity : ℕ) (choices : List (ℕ × ℕ))
    (remaining : ℕ) (sum : ℤ) (sq zeroCount : ℕ)
    (negatives positives : List ℤ)
    (hlength : choices.length ≤ 17)
    (hcount :
      a15MagnitudeChoiceUsed choices + zeroCount = remaining)
    (hsum :
      sum + a15MagnitudeChoiceSum choices =
        e7ComponentTargetSum parity)
    (hsq :
      sq + a15MagnitudeChoiceSq choices ≤
        e7ComponentTargetSq parity)
    (hspecial :
      parity = 1 → choices.length = 17 →
        choices.head?.map Prod.snd = some 0) :
    e7ScaleReducedProfile parity
        (negatives ++ a15MagnitudeChoiceNegatives choices ++
          List.replicate zeroCount 0 ++
          a15MagnitudeChoicePositives choices ++ positives) ∈
      e7EnumerateComponentsByMagnitudeAux parity choices.length remaining
        sum sq negatives positives := by
  induction choices generalizing remaining sum sq negatives positives with
  | nil =>
      simp only [a15MagnitudeChoiceUsed, zero_add] at hcount
      simp only [a15MagnitudeChoiceSum, add_zero] at hsum
      simp only [a15MagnitudeChoiceSq, add_zero] at hsq
      subst remaining
      rw [hsum]
      simp [e7EnumerateComponentsByMagnitudeAux, hsq,
        a15MagnitudeChoiceNegatives, a15MagnitudeChoicePositives]
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
            e7ComponentTargetSum parity := by
        simpa only [a15MagnitudeChoiceSum, m, Nat.cast_add,
          Nat.cast_one, add_assoc] using hsum
      have htailSq :
          (sq + (negativeCount + positiveCount) * m ^ 2) +
              a15MagnitudeChoiceSq choices ≤
            e7ComponentTargetSq parity := by
        simpa only [a15MagnitudeChoiceSq, m, add_assoc] using hsq
      have hfeasible :
          e7ComponentMagnitudeFeasible parity m
            (remaining - (negativeCount + positiveCount))
            (sum +
              ((positiveCount : ℤ) - negativeCount) * (m : ℤ))
            (sq + (negativeCount + positiveCount) * m ^ 2) = true := by
        unfold e7ComponentMagnitudeFeasible
        simp only [decide_eq_true_eq]
        have hsumBound := a15MagnitudeChoiceSum_natAbs_le choices
        have hmSub : m - 1 = choices.length := by
          simp [m]
        have hremainingEq :
            remaining - (negativeCount + positiveCount) =
              a15MagnitudeChoiceUsed choices + zeroCount :=
          htailCount.symm
        constructor
        · omega
        · rw [hmSub]
          have hdiff :
              e7ComponentTargetSum parity -
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
          exact hsumBound.trans (Nat.mul_le_mul_right _ husedLe)
      have hpositiveBound :
          positiveCount <
            (if parity = 1 && m = 17 then 0
              else remaining - negativeCount) + 1 := by
        by_cases hcase : parity = 1 ∧ m = 17
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
          parity = 1 → choices.length = 17 →
            choices.head?.map Prod.snd = some 0 := by
        intro _ hseventeen
        omega
      have hmemTail :=
        ih (remaining - (negativeCount + positiveCount))
          (sum +
            ((positiveCount : ℤ) - negativeCount) * (m : ℤ))
          (sq + (negativeCount + positiveCount) * m ^ 2)
          (negatives ++
            List.replicate negativeCount (-((m : ℕ) : ℤ)))
          (List.replicate positiveCount ((m : ℕ) : ℤ) ++ positives)
          htailLength htailCount htailSum htailSq htailSpecial
      have hfeasible' :
          e7ComponentMagnitudeFeasible parity (choices.length + 1)
            (remaining - (negativeCount + positiveCount))
            (sum +
              ((positiveCount : ℤ) - negativeCount) *
                ((choices.length : ℤ) + 1))
            (sq + (negativeCount + positiveCount) *
              (choices.length + 1) ^ 2) = true := by
        simpa only [m, Nat.cast_add, Nat.cast_one] using hfeasible
      simp only [List.length_cons,
        e7EnumerateComponentsByMagnitudeAux, List.mem_flatMap,
        a15MagnitudeChoiceNegatives, a15MagnitudeChoicePositives]
      refine ⟨negativeCount, List.mem_range.mpr hnegative, ?_⟩
      refine ⟨positiveCount,
        List.mem_range.mpr hpositiveBound, ?_⟩
      simp only [hfeasible', if_true]
      simpa only [m, Nat.cast_add, Nat.cast_one,
        Nat.add_sub_cancel_left, List.append_assoc] using hmemTail

/-- A bounded reduced coordinate list satisfying one component's exact
invariants emits its count-canonical representative. -/
theorem e7_canonical_reduced_component_mem_enumeration
    (parity : ℕ) (coordinates : List ℤ)
    (hlength : coordinates.length = 8)
    (hbounds : ∀ z ∈ coordinates, -17 ≤ z ∧ z ≤ 17)
    (hsum : coordinates.sum = e7ComponentTargetSum parity)
    (hsq :
      (coordinates.map (fun z : ℤ => z * z)).sum ≤
        e7ComponentTargetSq parity)
    (hspecial : parity = 1 → coordinates.count 17 = 0) :
    e7ScaleReducedProfile parity
        (a15CanonicalReducedCoordinates coordinates) ∈
      e7EnumerateComponentsByMagnitudeAux parity 17 8 0 0 [] [] := by
  let choices := a15MagnitudeChoicesFrom coordinates 17
  have hchoicesLength : choices.length = 17 := by simp [choices]
  have hperm :=
    a15CanonicalReducedCoordinates_perm coordinates hbounds
  have hcanonicalLength :
      (a15CanonicalReducedCoordinates coordinates).length = 8 :=
    hperm.length_eq.trans hlength
  have hcount :
      a15MagnitudeChoiceUsed choices + coordinates.count 0 = 8 := by
    rw [← a15CanonicalReducedCoordinates_length coordinates]
    exact hcanonicalLength
  have hchoiceSum :
      a15MagnitudeChoiceSum choices =
        e7ComponentTargetSum parity := by
    rw [← a15CanonicalReducedCoordinates_sum coordinates]
    exact hperm.sum_eq.trans hsum
  have hsqPerm :
      ((a15CanonicalReducedCoordinates coordinates).map
          (fun z : ℤ => z * z)).sum =
        (coordinates.map (fun z : ℤ => z * z)).sum :=
    (hperm.map (fun z : ℤ => z * z)).sum_eq
  have hchoiceSq :
      a15MagnitudeChoiceSq choices ≤ e7ComponentTargetSq parity := by
    have hchoiceSqInt :
        (a15MagnitudeChoiceSq choices : ℤ) ≤
          e7ComponentTargetSq parity := by
      rw [← a15CanonicalReducedCoordinates_sq_sum coordinates,
        hsqPerm]
      exact_mod_cast hsq
    exact_mod_cast hchoiceSqInt
  have hchoiceSpecial :
      parity = 1 → choices.length = 17 →
        choices.head?.map Prod.snd = some 0 := by
    intro hparity _
    simp only [choices, a15MagnitudeChoicesFrom, List.head?_cons,
      Option.map_some]
    exact congrArg some (hspecial hparity)
  have hmem :=
    e7EnumerateComponentsByMagnitudeAux_contains_of_choices
      parity choices 8 0 0 (coordinates.count 0) [] []
      (by omega) hcount (by simpa using hchoiceSum)
      (by simpa using hchoiceSq) hchoiceSpecial
  rw [hchoicesLength] at hmem
  simpa only [a15CanonicalReducedCoordinates, choices,
    List.nil_append, List.append_nil] using hmem

end SRG266
