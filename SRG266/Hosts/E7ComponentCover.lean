/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.E7FastComponentKey

/-!
# A chunkable coverage sweep over the enumerated E7 component profiles

`e7EnumerateComponentsByMagnitudeAux` *builds* a list of 120,036 profiles.
Materialising that list in the kernel is far too expensive, so this module
supplies `e7CoverAux`: the same magnitude recursion, but folding a Boolean
test over the leaves instead of collecting them.  `e7CoverAux_sound` turns a
single Boolean fact into a property of every enumerated profile.

The sweep is chunked: `e7CoverPrefix` stops the recursion at an explicitly
listed frontier of states. Checking the
prefix is cheap, and each frontier state becomes an independent chunk whose
`e7CoverAux` fact is discharged in its own module.
-/

namespace SRG266

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The magnitude recursion of `e7EnumerateComponentsByMagnitudeAux`, folding
a leaf test instead of collecting profiles. -/
def e7CoverAux (ok : Array ℤ → Bool) (parity : ℕ) :
    (m remaining : ℕ) → (sum : ℤ) → (sq : ℕ) →
      List ℤ → List ℤ → Bool
  | 0, remaining, sum, sq, negatives, positives =>
      if sum = e7ComponentTargetSum parity &&
          decide (sq ≤ e7ComponentTargetSq parity) then
        ok (e7ScaleReducedProfile parity
          (negatives ++ List.replicate remaining 0 ++ positives))
      else
        true
  | m + 1, remaining, sum, sq, negatives, positives =>
      (List.range (remaining + 1)).all fun negativeCount =>
        let positiveBound :=
          if parity = 1 && m + 1 = 17 then 0
          else remaining - negativeCount
        (List.range (positiveBound + 1)).all fun positiveCount =>
          let used := negativeCount + positiveCount
          let newRemaining := remaining - used
          let signedMultiplicity : ℤ :=
            (positiveCount : ℤ) - negativeCount
          let newSum := sum + signedMultiplicity * (m + 1)
          let newSq := sq + used * (m + 1) ^ 2
          if e7ComponentMagnitudeFeasible parity (m + 1)
              newRemaining newSum newSq then
            e7CoverAux ok parity m newRemaining newSum newSq
              (negatives ++
                List.replicate negativeCount (-((m + 1 : ℕ) : ℤ)))
              (List.replicate positiveCount ((m + 1 : ℕ) : ℤ) ++
                positives)
          else
            true

/-- A verified sweep certifies the leaf test on every enumerated profile. -/
theorem e7CoverAux_sound (ok : Array ℤ → Bool) (parity : ℕ) :
    ∀ (m remaining : ℕ) (sum : ℤ) (sq : ℕ) (negatives positives : List ℤ),
      e7CoverAux ok parity m remaining sum sq negatives positives = true →
      ∀ profile ∈
        e7EnumerateComponentsByMagnitudeAux parity m remaining sum sq
          negatives positives,
        ok profile = true := by
  intro m
  induction m with
  | zero =>
      intro remaining sum sq negatives positives hcover profile hprofile
      by_cases hleaf :
          (sum = e7ComponentTargetSum parity &&
            decide (sq ≤ e7ComponentTargetSq parity)) = true
      · simp only [e7EnumerateComponentsByMagnitudeAux, hleaf, if_true,
          List.mem_singleton] at hprofile
        simp only [e7CoverAux, hleaf, if_true] at hcover
        rw [hprofile]
        exact hcover
      · rw [Bool.not_eq_true] at hleaf
        simp only [e7EnumerateComponentsByMagnitudeAux, hleaf,
          Bool.false_eq_true, if_false, List.not_mem_nil] at hprofile
  | succ m ih =>
      intro remaining sum sq negatives positives hcover profile hprofile
      simp only [e7EnumerateComponentsByMagnitudeAux,
        List.mem_flatMap] at hprofile
      obtain ⟨negativeCount, hneg, hprofile⟩ := hprofile
      obtain ⟨positiveCount, hpos, hprofile⟩ := hprofile
      simp only [e7CoverAux, List.all_eq_true] at hcover
      have hstep := hcover negativeCount hneg positiveCount hpos
      split at hprofile
      · rename_i hfeasible
        rw [if_pos hfeasible] at hstep
        exact ih _ _ _ _ _ hstep profile hprofile
      · simp only [List.not_mem_nil] at hprofile

/-- One state of the magnitude recursion, used to cut the sweep into chunks. -/
structure E7CoverState where
  /-- Highest magnitude still to be distributed. -/
  m : ℕ
  /-- Coordinates still to be filled. -/
  remaining : ℕ
  /-- Coordinate sum accumulated so far. -/
  sum : ℤ
  /-- Squared norm accumulated so far. -/
  sq : ℕ
  /-- Negative coordinates fixed so far. -/
  negatives : List ℤ
  /-- Positive coordinates fixed so far. -/
  positives : List ℤ
  deriving DecidableEq

/-- The sweep below one recursion state. -/
def e7CoverAuxState
    (ok : Array ℤ → Bool) (parity : ℕ) (state : E7CoverState) : Bool :=
  e7CoverAux ok parity state.m state.remaining state.sum state.sq
    state.negatives state.positives

/-- The magnitude recursion cut off at an explicit frontier of states. -/
def e7CoverPrefix
    (ok : Array ℤ → Bool) (frontier : List E7CoverState) (parity : ℕ) :
    (m remaining : ℕ) → (sum : ℤ) → (sq : ℕ) →
      List ℤ → List ℤ → Bool
  | 0, remaining, sum, sq, negatives, positives =>
      if (⟨0, remaining, sum, sq, negatives, positives⟩ : E7CoverState) ∈
          frontier then
        true
      else if sum = e7ComponentTargetSum parity &&
          decide (sq ≤ e7ComponentTargetSq parity) then
        ok (e7ScaleReducedProfile parity
          (negatives ++ List.replicate remaining 0 ++ positives))
      else
        true
  | m + 1, remaining, sum, sq, negatives, positives =>
      if (⟨m + 1, remaining, sum, sq, negatives, positives⟩ : E7CoverState) ∈
          frontier then
        true
      else
        (List.range (remaining + 1)).all fun negativeCount =>
          let positiveBound :=
            if parity = 1 && m + 1 = 17 then 0
            else remaining - negativeCount
          (List.range (positiveBound + 1)).all fun positiveCount =>
            let used := negativeCount + positiveCount
            let newRemaining := remaining - used
            let signedMultiplicity : ℤ :=
              (positiveCount : ℤ) - negativeCount
            let newSum := sum + signedMultiplicity * (m + 1)
            let newSq := sq + used * (m + 1) ^ 2
            if e7ComponentMagnitudeFeasible parity (m + 1)
                newRemaining newSum newSq then
              e7CoverPrefix ok frontier parity m newRemaining newSum newSq
                (negatives ++
                  List.replicate negativeCount (-((m + 1 : ℕ) : ℤ)))
                (List.replicate positiveCount ((m + 1 : ℕ) : ℤ) ++
                  positives)
            else
              true

/-- A verified prefix together with a verified sweep below every frontier
state reconstructs the full sweep. -/
theorem e7CoverAux_of_prefix
    (ok : Array ℤ → Bool) (frontier : List E7CoverState) (parity : ℕ)
    (hfrontier : ∀ state ∈ frontier, e7CoverAuxState ok parity state = true) :
    ∀ (m remaining : ℕ) (sum : ℤ) (sq : ℕ) (negatives positives : List ℤ),
      e7CoverPrefix ok frontier parity m remaining sum sq
          negatives positives = true →
      e7CoverAux ok parity m remaining sum sq negatives positives = true := by
  intro m
  induction m with
  | zero =>
      intro remaining sum sq negatives positives hprefix
      by_cases hmem :
          (⟨0, remaining, sum, sq, negatives, positives⟩ : E7CoverState) ∈
            frontier
      · have := hfrontier _ hmem
        simpa only [e7CoverAuxState] using this
      · simp only [e7CoverPrefix, hmem, if_false] at hprefix
        simpa only [e7CoverAux] using hprefix
  | succ m ih =>
      intro remaining sum sq negatives positives hprefix
      by_cases hmem :
          (⟨m + 1, remaining, sum, sq, negatives, positives⟩ : E7CoverState) ∈
            frontier
      · have := hfrontier _ hmem
        simpa only [e7CoverAuxState] using this
      · simp only [e7CoverPrefix, hmem, if_false, List.all_eq_true] at hprefix
        simp only [e7CoverAux, List.all_eq_true]
        intro negativeCount hneg positiveCount hpos
        have hstep := hprefix negativeCount hneg positiveCount hpos
        split
        · rename_i hfeasible
          rw [if_pos hfeasible] at hstep
          exact ih _ _ _ _ _ hstep
        · rfl

/-- Both parities of the enumeration, from two verified sweeps. -/
theorem e7EnumeratedComponentProfiles_forall
    (ok : Array ℤ → Bool)
    (heven : e7CoverAux ok 0 17 8 0 0 [] [] = true)
    (hodd : e7CoverAux ok 1 17 8 0 0 [] [] = true) :
    ∀ profile ∈ e7EnumeratedComponentProfiles, ok profile = true := by
  intro profile hprofile
  simp only [e7EnumeratedComponentProfiles, List.mem_append] at hprofile
  rcases hprofile with h | h
  · exact e7CoverAux_sound ok 0 17 8 0 0 [] [] heven profile h
  · exact e7CoverAux_sound ok 1 17 8 0 0 [] [] hodd profile h

end SRG266
