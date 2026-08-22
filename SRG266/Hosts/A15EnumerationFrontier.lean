/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.A15PolyEnumeration

/-!
# Splitting the A15 magnitude search at a frontier

The A15 magnitude search visits 1,796,107 recursion nodes, far more than one
kernel reduction can carry.  This module cuts the search at a chosen depth.

`a15Frontier` runs exactly the branching of `a15PolyEnumerateByMagnitudeAux`
for `depth` magnitude levels and then records the state it reached instead of
recursing further.  `a15PolyEnumerateByMagnitudeAux_eq_frontier` says the
search is the concatenation of the searches started from the recorded states:

  `search (m + depth) st = expand m (frontier (m + depth) depth st)`.

Applying this twice -- once from magnitude seventeen to magnitude eleven and
once from magnitude eleven to magnitude five -- exposes 5,679 independent
subtrees whose combined output can be certified module by module.  Because
`List.flatMap` distributes over `++`, the frontier list may then be presented
as an explicit concatenation of chunk lists, and the chunk certificates glue
without any further evaluation.

Nothing in this module is evaluated.
-/

namespace SRG266

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- A state of the magnitude recursion: the coordinates still to be chosen,
the accumulated sum and squared norm, and the negative and positive
coordinates fixed so far. -/
structure A15MagState where
  /-- Coordinates still to be assigned. -/
  remaining : ℕ
  /-- Sum of the coordinates fixed so far. -/
  sum : ℤ
  /-- Squared norm of the coordinates fixed so far. -/
  sq : ℕ
  /-- Negative coordinates fixed so far, in increasing order. -/
  negatives : List ℤ
  /-- Positive coordinates fixed so far, in increasing order. -/
  positives : List ℤ
  deriving DecidableEq, Repr

/-- The search below one recorded state. -/
def a15PolySubtree (residue : ℤ) (m : ℕ) (st : A15MagState) : List (Array ℤ) :=
  a15PolyEnumerateByMagnitudeAux residue m st.remaining st.sum st.sq
    st.negatives st.positives

/-- The search below a whole list of recorded states. -/
def a15PolyExpand (residue : ℤ) (m : ℕ) (states : List A15MagState) :
    List (Array ℤ) :=
  states.flatMap (a15PolySubtree residue m)

theorem a15PolyExpand_append (residue : ℤ) (m : ℕ)
    (states₁ states₂ : List A15MagState) :
    a15PolyExpand residue m (states₁ ++ states₂) =
      a15PolyExpand residue m states₁ ++ a15PolyExpand residue m states₂ :=
  List.flatMap_append ..

/-- The states reached after `depth` magnitude levels of the search. -/
def a15Frontier (residue : ℤ) :
    (m depth remaining : ℕ) → (sum : ℤ) → (sq : ℕ) →
      List ℤ → List ℤ → List A15MagState
  | _, 0, remaining, sum, sq, negatives, positives =>
      [⟨remaining, sum, sq, negatives, positives⟩]
  | 0, _ + 1, remaining, sum, sq, negatives, positives =>
      [⟨remaining, sum, sq, negatives, positives⟩]
  | m + 1, d + 1, remaining, sum, sq, negatives, positives =>
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
            a15Frontier residue m d newRemaining newSum newSq
              (negatives ++
                List.replicate negativeCount (-((m + 1 : ℕ) : ℤ)))
              (List.replicate positiveCount ((m + 1 : ℕ) : ℤ) ++
                positives)
          else
            []

/-- The search is the concatenation of the searches started from the states
its own branching reaches after `depth` magnitude levels. -/
theorem a15PolyEnumerateByMagnitudeAux_eq_frontier (residue : ℤ) (m : ℕ) :
    ∀ (depth remaining : ℕ) (sum : ℤ) (sq : ℕ) (negatives positives : List ℤ),
      a15PolyEnumerateByMagnitudeAux residue (m + depth) remaining sum sq
          negatives positives =
        a15PolyExpand residue m
          (a15Frontier residue (m + depth) depth remaining sum sq negatives
            positives) := by
  intro depth
  induction depth with
  | zero =>
      intro remaining sum sq negatives positives
      simp [a15PolyExpand, a15Frontier, a15PolySubtree]
  | succ depth ih =>
      intro remaining sum sq negatives positives
      rw [show m + (depth + 1) = (m + depth) + 1 by omega]
      unfold a15PolyEnumerateByMagnitudeAux a15Frontier
      rw [a15PolyExpand, List.flatMap_assoc]
      refine List.flatMap_congr ?_
      intro negativeCount _
      simp only []
      rw [List.flatMap_assoc]
      refine List.flatMap_congr ?_
      intro positiveCount _
      split_ifs with hfeas
      · exact ih _ _ _ _ _
      · simp

end SRG266
