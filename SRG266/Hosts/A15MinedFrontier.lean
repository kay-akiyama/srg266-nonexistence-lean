/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.A15MinedNormSearch

/-!
# A bounded frontier for the mined A15 search

This module splits the structurally complete norm-48 magnitude recursion into
independent residual subtrees. No search result is evaluated here.
-/

namespace SRG266

set_option maxRecDepth 100000

/-! ## A bounded frontier for kernel evaluation -/

/-- A recorded state of the divided norm-48 magnitude recursion. -/
structure A15SmallMagState where
  remaining : ℕ
  sum : ℤ
  sq : ℕ
  negatives : List ℤ
  positives : List ℤ
  deriving DecidableEq, Repr

/-- The residual search below one recorded small-profile state. -/
def a15SmallSubtree (m : ℕ) (st : A15SmallMagState) : List (List ℤ) :=
  a15SmallEnumerateByMagnitudeAux m st.remaining st.sum st.sq
    st.negatives st.positives

/-- Concatenation of the residual searches below a state list. -/
def a15SmallExpand (m : ℕ) (states : List A15SmallMagState) :
    List (List ℤ) :=
  states.flatMap (a15SmallSubtree m)

theorem a15SmallExpand_append (m : ℕ)
    (states₁ states₂ : List A15SmallMagState) :
    a15SmallExpand m (states₁ ++ states₂) =
      a15SmallExpand m states₁ ++ a15SmallExpand m states₂ :=
  List.flatMap_append ..

/-- States reached after the requested number of magnitude levels. -/
def a15SmallFrontier :
    (m depth remaining : ℕ) → (sum : ℤ) → (sq : ℕ) →
      List ℤ → List ℤ → List A15SmallMagState
  | _, 0, remaining, sum, sq, negatives, positives =>
      [⟨remaining, sum, sq, negatives, positives⟩]
  | 0, _ + 1, remaining, sum, sq, negatives, positives =>
      [⟨remaining, sum, sq, negatives, positives⟩]
  | m + 1, d + 1, remaining, sum, sq, negatives, positives =>
      (List.range (remaining + 1)).flatMap fun negativeCount =>
        (List.range (remaining - negativeCount + 1)).flatMap fun positiveCount =>
          let used := negativeCount + positiveCount
          let newRemaining := remaining - used
          let signedMultiplicity : ℤ :=
            (positiveCount : ℤ) - negativeCount
          let newSum := sum + signedMultiplicity * (m + 1)
          let newSq := sq + used * (m + 1) ^ 2
          if a15SmallMagnitudeFeasible (m + 1) newRemaining newSum newSq then
            a15SmallFrontier m d newRemaining newSum newSq
              (negatives ++
                List.replicate negativeCount (-((m + 1 : ℕ) : ℤ)))
              (List.replicate positiveCount ((m + 1 : ℕ) : ℤ) ++
                positives)
          else
            []

/-- The search is the expansion of every state at any bounded frontier. -/
theorem a15SmallEnumerateByMagnitudeAux_eq_frontier (m : ℕ) :
    ∀ (depth remaining : ℕ) (sum : ℤ) (sq : ℕ)
        (negatives positives : List ℤ),
      a15SmallEnumerateByMagnitudeAux (m + depth) remaining sum sq
          negatives positives =
        a15SmallExpand m
          (a15SmallFrontier (m + depth) depth remaining sum sq negatives
            positives) := by
  intro depth
  induction depth with
  | zero =>
      intro remaining sum sq negatives positives
      simp [a15SmallExpand, a15SmallFrontier, a15SmallSubtree]
  | succ depth ih =>
      intro remaining sum sq negatives positives
      rw [show m + (depth + 1) = (m + depth) + 1 by omega]
      unfold a15SmallEnumerateByMagnitudeAux a15SmallFrontier
      rw [a15SmallExpand, List.flatMap_assoc]
      refine List.flatMap_congr ?_
      intro negativeCount _
      simp only []
      rw [List.flatMap_assoc]
      refine List.flatMap_congr ?_
      intro positiveCount _
      split_ifs with hfeasible
      · exact ih _ _ _ _ _
      · simp

end SRG266
