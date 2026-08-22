/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.E7MinedNormSearch

/-!
# A bounded frontier for the mined E7 norm search

The frontier separates the magnitude recursion into independent residual
subtrees. No search result is evaluated in this theory module.
-/

namespace SRG266

set_option maxRecDepth 100000

structure E7MinedMagState where
  remaining : ℕ
  sum : ℤ
  sq : ℕ
  negatives : List ℤ
  positives : List ℤ
  deriving DecidableEq, Repr

def e7MinedSubtree (m : ℕ) (st : E7MinedMagState) : List (List ℤ) :=
  e7MinedEnumerateByMagnitudeAux m st.remaining st.sum st.sq
    st.negatives st.positives

def e7MinedExpand (m : ℕ) (states : List E7MinedMagState) :
    List (List ℤ) :=
  states.flatMap (e7MinedSubtree m)

theorem e7MinedExpand_append (m : ℕ)
    (states₁ states₂ : List E7MinedMagState) :
    e7MinedExpand m (states₁ ++ states₂) =
      e7MinedExpand m states₁ ++ e7MinedExpand m states₂ :=
  List.flatMap_append ..

def e7MinedFrontier :
    (m depth remaining : ℕ) → (sum : ℤ) → (sq : ℕ) →
      List ℤ → List ℤ → List E7MinedMagState
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
          if e7MinedMagnitudeFeasible (m + 1) newRemaining newSum newSq then
            e7MinedFrontier m d newRemaining newSum newSq
              (negatives ++
                List.replicate negativeCount (-((m + 1 : ℕ) : ℤ)))
              (List.replicate positiveCount ((m + 1 : ℕ) : ℤ) ++
                positives)
          else
            []

theorem e7MinedEnumerateByMagnitudeAux_eq_frontier (m : ℕ) :
    ∀ (depth remaining : ℕ) (sum : ℤ) (sq : ℕ)
        (negatives positives : List ℤ),
      e7MinedEnumerateByMagnitudeAux (m + depth) remaining sum sq
          negatives positives =
        e7MinedExpand m
          (e7MinedFrontier (m + depth) depth remaining sum sq negatives
            positives) := by
  intro depth
  induction depth with
  | zero =>
      intro remaining sum sq negatives positives
      simp [e7MinedExpand, e7MinedFrontier, e7MinedSubtree]
  | succ depth ih =>
      intro remaining sum sq negatives positives
      rw [show m + (depth + 1) = (m + depth) + 1 by omega]
      unfold e7MinedEnumerateByMagnitudeAux e7MinedFrontier
      rw [e7MinedExpand, List.flatMap_assoc]
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
