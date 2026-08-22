/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.E7ComponentEnumeration

/-!
# A chunkable filtering sweep over the enumerated E7 component profiles

`e7EnumerateComponentsByMagnitudeAux` builds a list of 120,036 profiles, which
is far beyond one kernel evaluation.  Almost all of those profiles are
irrelevant for the concrete expansion: only the profiles whose component key
is one of the finitely many listed keys ever enter a filter.

`e7FilterAux` runs the very same magnitude recursion but keeps only the leaves
passing a Boolean test, so the kernel never materialises the full list.
`e7FilterAux_eq` identifies it with `List.filter` over the enumeration, which
is what makes the chunked evaluation an *exact* description of every fibre,
not merely an over-approximation.

The sweep is chunked: `e7FilterPrefix` stops the recursion at an explicitly
listed frontier of states carrying their
own results.  Checking the prefix is cheap, and each frontier state becomes an
independent chunk discharged in its own module.
-/

namespace SRG266

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- `List.filter` commutes with `List.flatMap`. -/
theorem e7Filter_flatMap {α β : Type _} (l : List α) (f : α → List β)
    (ok : β → Bool) :
    (l.flatMap f).filter ok = l.flatMap fun a => (f a).filter ok := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      simp only [List.flatMap_cons, List.filter_append, ih]

/-- The magnitude recursion of `e7EnumerateComponentsByMagnitudeAux`, keeping
only the leaves accepted by `ok`. -/
def e7FilterAux (ok : Array ℤ → Bool) (parity : ℕ) :
    (m remaining : ℕ) → (sum : ℤ) → (sq : ℕ) →
      List ℤ → List ℤ → List (Array ℤ)
  | 0, remaining, sum, sq, negatives, positives =>
      if sum = e7ComponentTargetSum parity &&
          decide (sq ≤ e7ComponentTargetSq parity) then
        (if ok (e7ScaleReducedProfile parity
              (negatives ++ List.replicate remaining 0 ++ positives)) then
          [e7ScaleReducedProfile parity
            (negatives ++ List.replicate remaining 0 ++ positives)]
        else [])
      else
        []
  | m + 1, remaining, sum, sq, negatives, positives =>
      (List.range (remaining + 1)).flatMap fun negativeCount =>
        let positiveBound :=
          if parity = 1 && m + 1 = 17 then 0
          else remaining - negativeCount
        (List.range (positiveBound + 1)).flatMap fun positiveCount =>
          let used := negativeCount + positiveCount
          let newRemaining := remaining - used
          let signedMultiplicity : ℤ :=
            (positiveCount : ℤ) - negativeCount
          let newSum := sum + signedMultiplicity * (m + 1)
          let newSq := sq + used * (m + 1) ^ 2
          if e7ComponentMagnitudeFeasible parity (m + 1)
              newRemaining newSum newSq then
            e7FilterAux ok parity m newRemaining newSum newSq
              (negatives ++
                List.replicate negativeCount (-((m + 1 : ℕ) : ℤ)))
              (List.replicate positiveCount ((m + 1 : ℕ) : ℤ) ++
                positives)
          else
            []

/-- The filtering sweep is exactly `List.filter` over the enumeration.  The
proof is structural: no subtree is ever evaluated. -/
theorem e7FilterAux_eq (ok : Array ℤ → Bool) (parity : ℕ) :
    ∀ (m remaining : ℕ) (sum : ℤ) (sq : ℕ) (negatives positives : List ℤ),
      e7FilterAux ok parity m remaining sum sq negatives positives =
        (e7EnumerateComponentsByMagnitudeAux parity m remaining sum sq
          negatives positives).filter ok := by
  intro m
  induction m with
  | zero =>
      intro remaining sum sq negatives positives
      simp only [e7FilterAux, e7EnumerateComponentsByMagnitudeAux]
      split
      · split <;> simp_all
      · rfl
  | succ m ih =>
      intro remaining sum sq negatives positives
      simp only [e7FilterAux, e7EnumerateComponentsByMagnitudeAux,
        e7Filter_flatMap]
      refine congrFun (congrArg List.flatMap (funext fun negativeCount => ?_)) _
      refine congrFun (congrArg List.flatMap (funext fun positiveCount => ?_)) _
      split
      · exact ih _ _ _ _ _
      · rfl

/-- Every enumerated component profile has eight coordinates. -/
theorem e7EnumerateComponentsByMagnitudeAux_size (parity : ℕ) :
    ∀ (m remaining : ℕ) (sum : ℤ) (sq : ℕ) (negatives positives : List ℤ),
      negatives.length + remaining + positives.length = 8 →
      ∀ profile ∈
        e7EnumerateComponentsByMagnitudeAux parity m remaining sum sq
          negatives positives,
        profile.size = 8 := by
  intro m
  induction m with
  | zero =>
      intro remaining sum sq negatives positives hlength profile hprofile
      simp only [e7EnumerateComponentsByMagnitudeAux] at hprofile
      split at hprofile
      · simp only [List.mem_singleton] at hprofile
        subst hprofile
        simp only [e7ScaleReducedProfile, List.size_toArray, List.length_map,
          List.length_append, List.length_replicate]
        omega
      · simp only [List.not_mem_nil] at hprofile
  | succ m ih =>
      intro remaining sum sq negatives positives hlength profile hprofile
      simp only [e7EnumerateComponentsByMagnitudeAux,
        List.mem_flatMap, List.mem_range] at hprofile
      obtain ⟨negativeCount, hneg, hprofile⟩ := hprofile
      obtain ⟨positiveCount, hpos, hprofile⟩ := hprofile
      split at hprofile
      · refine ih _ _ _ _ _ ?_ profile hprofile
        have hbound : positiveCount ≤ remaining - negativeCount := by
          split at hpos <;> omega
        simp only [List.length_append, List.length_replicate]
        omega
      · simp only [List.not_mem_nil] at hprofile

/-- Every enumerated component profile has eight coordinates. -/
theorem e7EnumeratedComponentProfiles_size (profile : Array ℤ)
    (hprofile : profile ∈ e7EnumeratedComponentProfiles) :
    profile.size = 8 := by
  simp only [e7EnumeratedComponentProfiles, List.mem_append] at hprofile
  rcases hprofile with h | h
  · exact e7EnumerateComponentsByMagnitudeAux_size 0 17 8 0 0 [] [] (by simp) profile h
  · exact e7EnumerateComponentsByMagnitudeAux_size 1 17 8 0 0 [] [] (by simp) profile h

/-- One state of the magnitude recursion, used to cut the sweep into chunks. -/
structure E7FilterState where
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

/-- The filtering sweep below one recursion state. -/
def e7FilterAuxState
    (ok : Array ℤ → Bool) (parity : ℕ) (state : E7FilterState) :
    List (Array ℤ) :=
  e7FilterAux ok parity state.m state.remaining state.sum state.sq
    state.negatives state.positives

/-- The filtering recursion cut off at an explicit frontier of states, each
carrying the result of its own subtree. -/
def e7FilterPrefix
    (ok : Array ℤ → Bool)
    (frontier : List (E7FilterState × List (Array ℤ))) (parity : ℕ) :
    (m remaining : ℕ) → (sum : ℤ) → (sq : ℕ) →
      List ℤ → List ℤ → List (Array ℤ)
  | 0, remaining, sum, sq, negatives, positives =>
      match frontier.find? fun entry =>
          decide (entry.1 =
            (⟨0, remaining, sum, sq, negatives, positives⟩ : E7FilterState)) with
      | some entry => entry.2
      | none =>
          if sum = e7ComponentTargetSum parity &&
              decide (sq ≤ e7ComponentTargetSq parity) then
            (if ok (e7ScaleReducedProfile parity
                  (negatives ++ List.replicate remaining 0 ++ positives)) then
              [e7ScaleReducedProfile parity
                (negatives ++ List.replicate remaining 0 ++ positives)]
            else [])
          else
            []
  | m + 1, remaining, sum, sq, negatives, positives =>
      match frontier.find? fun entry =>
          decide (entry.1 =
            (⟨m + 1, remaining, sum, sq, negatives, positives⟩ :
              E7FilterState)) with
      | some entry => entry.2
      | none =>
          (List.range (remaining + 1)).flatMap fun negativeCount =>
            let positiveBound :=
              if parity = 1 && m + 1 = 17 then 0
              else remaining - negativeCount
            (List.range (positiveBound + 1)).flatMap fun positiveCount =>
              let used := negativeCount + positiveCount
              let newRemaining := remaining - used
              let signedMultiplicity : ℤ :=
                (positiveCount : ℤ) - negativeCount
              let newSum := sum + signedMultiplicity * (m + 1)
              let newSq := sq + used * (m + 1) ^ 2
              if e7ComponentMagnitudeFeasible parity (m + 1)
                  newRemaining newSum newSq then
                e7FilterPrefix ok frontier parity m newRemaining newSum newSq
                  (negatives ++
                    List.replicate negativeCount (-((m + 1 : ℕ) : ℤ)))
                  (List.replicate positiveCount ((m + 1 : ℕ) : ℤ) ++
                    positives)
              else
                []

/-- A verified prefix together with a verified sweep below every frontier
state reconstructs the full filtering sweep. -/
theorem e7FilterAux_of_prefix
    (ok : Array ℤ → Bool)
    (frontier : List (E7FilterState × List (Array ℤ))) (parity : ℕ)
    (hfrontier : ∀ entry ∈ frontier,
      e7FilterAuxState ok parity entry.1 = entry.2) :
    ∀ (m remaining : ℕ) (sum : ℤ) (sq : ℕ) (negatives positives : List ℤ),
      e7FilterPrefix ok frontier parity m remaining sum sq
          negatives positives =
        e7FilterAux ok parity m remaining sum sq negatives positives := by
  have hentry : ∀ (state : E7FilterState) (entry : E7FilterState × List (Array ℤ)),
      frontier.find? (fun entry => decide (entry.1 = state)) = some entry →
      e7FilterAuxState ok parity state = entry.2 := by
    intro state entry hfind
    have hmem := List.mem_of_find?_eq_some hfind
    have heq := List.find?_some hfind
    simp only [decide_eq_true_eq] at heq
    rw [← heq]
    exact hfrontier entry hmem
  intro m
  induction m with
  | zero =>
      intro remaining sum sq negatives positives
      simp only [e7FilterPrefix]
      split
      · rename_i entry hfind
        have := hentry ⟨0, remaining, sum, sq, negatives, positives⟩ entry hfind
        simpa only [e7FilterAuxState] using this.symm
      · simp only [e7FilterAux]
  | succ m ih =>
      intro remaining sum sq negatives positives
      simp only [e7FilterPrefix]
      split
      · rename_i entry hfind
        have := hentry ⟨m + 1, remaining, sum, sq, negatives, positives⟩ entry hfind
        simpa only [e7FilterAuxState] using this.symm
      · simp only [e7FilterAux]
        refine congrFun (congrArg List.flatMap (funext fun negativeCount => ?_)) _
        refine congrFun (congrArg List.flatMap (funext fun positiveCount => ?_)) _
        split
        · exact ih _ _ _ _ _
        · rfl

/-- Both parities of the enumeration, from two verified filtering sweeps. -/
theorem e7EnumeratedComponentProfiles_filter
    (ok : Array ℤ → Bool) :
    e7EnumeratedComponentProfiles.filter ok =
      e7FilterAux ok 0 17 8 0 0 [] [] ++ e7FilterAux ok 1 17 8 0 0 [] [] := by
  simp only [e7EnumeratedComponentProfiles, List.filter_append,
    e7FilterAux_eq]

end SRG266
