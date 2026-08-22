/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.A15CentroidSolution

/-!
# Lightweight signed-magnitude paths

These definitions and pruning bounds are shared by the A15/E7
enumerators and the mined small-profile search.  They have no dependency on
generated enumeration or centroid-certificate data.
-/

namespace SRG266

set_option maxRecDepth 100000

/-- Total number of nonzero coordinates prescribed by a magnitude path. -/
def a15MagnitudeChoiceUsed : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (negativeCount, positiveCount) :: choices =>
      negativeCount + positiveCount + a15MagnitudeChoiceUsed choices

/-- Signed coordinate sum prescribed by a path. -/
def a15MagnitudeChoiceSum : List (ℕ × ℕ) → ℤ
  | [] => 0
  | (negativeCount, positiveCount) :: choices =>
      ((positiveCount : ℤ) - negativeCount) * (choices.length + 1) +
        a15MagnitudeChoiceSum choices

/-- Squared norm prescribed by a magnitude path. -/
def a15MagnitudeChoiceSq : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (negativeCount, positiveCount) :: choices =>
      (negativeCount + positiveCount) * (choices.length + 1) ^ 2 +
        a15MagnitudeChoiceSq choices

/-- Negative coordinates produced by a path, in nondecreasing order. -/
def a15MagnitudeChoiceNegatives : List (ℕ × ℕ) → List ℤ
  | [] => []
  | (negativeCount, _) :: choices =>
      List.replicate negativeCount (-((choices.length + 1 : ℕ) : ℤ)) ++
        a15MagnitudeChoiceNegatives choices

/-- Positive coordinates produced by a path, in nondecreasing order. -/
def a15MagnitudeChoicePositives : List (ℕ × ℕ) → List ℤ
  | [] => []
  | (_, positiveCount) :: choices =>
      a15MagnitudeChoicePositives choices ++
        List.replicate positiveCount ((choices.length + 1 : ℕ) : ℤ)

theorem a15MagnitudeChoiceSq_le
    (choices : List (ℕ × ℕ)) :
    a15MagnitudeChoiceSq choices ≤
      a15MagnitudeChoiceUsed choices * choices.length ^ 2 := by
  induction choices with
  | nil => simp [a15MagnitudeChoiceSq, a15MagnitudeChoiceUsed]
  | cons choice choices ih =>
      rcases choice with ⟨negativeCount, positiveCount⟩
      simp only [a15MagnitudeChoiceSq, a15MagnitudeChoiceUsed,
        List.length_cons]
      have hlength : choices.length ^ 2 ≤ (choices.length + 1) ^ 2 :=
        Nat.pow_le_pow_left (Nat.le_succ choices.length) 2
      calc
        (negativeCount + positiveCount) * (choices.length + 1) ^ 2 +
              a15MagnitudeChoiceSq choices
            ≤ (negativeCount + positiveCount) *
                (choices.length + 1) ^ 2 +
              a15MagnitudeChoiceUsed choices * choices.length ^ 2 :=
          Nat.add_le_add_left ih _
        _ ≤ (negativeCount + positiveCount) *
                (choices.length + 1) ^ 2 +
              a15MagnitudeChoiceUsed choices *
                (choices.length + 1) ^ 2 := by
          exact Nat.add_le_add_left
            (Nat.mul_le_mul_left _ hlength) _
        _ = (negativeCount + positiveCount +
              a15MagnitudeChoiceUsed choices) *
                (choices.length + 1) ^ 2 := by ring

private theorem natAbs_sub_natCast_le_add (a b : ℕ) :
    Int.natAbs ((a : ℤ) - b) ≤ a + b := by
  rw [← Int.ofNat_le, Int.natCast_natAbs]
  exact abs_le.mpr ⟨by omega, by omega⟩

theorem a15MagnitudeChoiceSum_natAbs_le
    (choices : List (ℕ × ℕ)) :
    (a15MagnitudeChoiceSum choices).natAbs ≤
      a15MagnitudeChoiceUsed choices * choices.length := by
  induction choices with
  | nil => simp [a15MagnitudeChoiceSum, a15MagnitudeChoiceUsed]
  | cons choice choices ih =>
      rcases choice with ⟨negativeCount, positiveCount⟩
      let m := choices.length + 1
      have hhead :
          (((positiveCount : ℤ) - negativeCount) * (m : ℤ)).natAbs ≤
            (positiveCount + negativeCount) * m := by
        rw [Int.natAbs_mul]
        exact Nat.mul_le_mul_right m
          (natAbs_sub_natCast_le_add positiveCount negativeCount)
      have htriangle :=
        Int.natAbs_add_le
          (((positiveCount : ℤ) - negativeCount) * (m : ℤ))
          (a15MagnitudeChoiceSum choices)
      simp only [a15MagnitudeChoiceSum, a15MagnitudeChoiceUsed,
        List.length_cons]
      calc
        Int.natAbs
              (((positiveCount : ℤ) - ↑negativeCount) *
                  ↑(choices.length + 1) +
                a15MagnitudeChoiceSum choices)
            ≤ Int.natAbs
                (((positiveCount : ℤ) - negativeCount) *
                  (m : ℤ)) +
              Int.natAbs (a15MagnitudeChoiceSum choices) := htriangle
        _ ≤ (positiveCount + negativeCount) * m +
              a15MagnitudeChoiceUsed choices * choices.length :=
          Nat.add_le_add hhead ih
        _ ≤ (positiveCount + negativeCount) * m +
              a15MagnitudeChoiceUsed choices * m := by
          exact Nat.add_le_add_left
            (Nat.mul_le_mul_left _ (Nat.le_succ choices.length)) _
        _ = (negativeCount + positiveCount +
              a15MagnitudeChoiceUsed choices) *
                (choices.length + 1) := by
          simp only [m]
          ring

end SRG266
