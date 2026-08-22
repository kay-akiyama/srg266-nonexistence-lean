/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.A15PolyCount

/-!
# The A15 magnitude search with the generating-function counter

`a15PolyEnumerateByMagnitudeAux` is `a15EnumerateByMagnitudeAux` with one
token changed: the eligible-shell counter queried against the threshold `74`
at a complete profile.  `a15_poly_fast_agree` says the two counters answer
that question identically on bounded length-sixteen reduced profiles, so a
structural induction on the magnitude parameter identifies the two searches
outright, with no evaluation at all.  The invariant to carry is that the
partial profile always has sixteen slots and coordinates bounded by
seventeen, which the recursion preserves because it only ever appends `±m`
with `m ≤ 17`.

The generating-function counter makes the 1,796,107-node search checkable in
bounded certificate modules.
-/

namespace SRG266

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The magnitude recursion with the generating-function eligible-shell
counter. -/
def a15PolyEnumerateByMagnitudeAux
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
            a15PolyEligibleCountReduced residue reduced) then
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
            a15PolyEnumerateByMagnitudeAux residue m newRemaining
              newSum newSq
              (negatives ++
                List.replicate negativeCount (-((m + 1 : ℕ) : ℤ)))
              (List.replicate positiveCount ((m + 1 : ℕ) : ℤ) ++
                positives)
          else
            []

/-- The two magnitude recursions coincide on every reachable state. -/
theorem a15PolyEnumerateByMagnitudeAux_eq (residue : ℤ)
    (hres : residue = 0 ∨ residue = 2) :
    ∀ (m remaining : ℕ) (sum : ℤ) (sq : ℕ) (negatives positives : List ℤ),
      m ≤ 17 →
      negatives.length + remaining + positives.length = 16 →
      (∀ z ∈ negatives, -17 ≤ z ∧ z ≤ 17) →
      (∀ z ∈ positives, -17 ≤ z ∧ z ≤ 17) →
      a15PolyEnumerateByMagnitudeAux residue m remaining sum sq negatives
          positives =
        a15EnumerateByMagnitudeAux residue m remaining sum sq negatives
          positives := by
  intro m
  induction m with
  | zero =>
      intro remaining sum sq negatives positives _ hlen hneg hpos
      unfold a15PolyEnumerateByMagnitudeAux a15EnumerateByMagnitudeAux
      have hlen' :
          (negatives ++ (List.replicate remaining 0 ++ positives)).length
            = 16 := by
        simp only [List.length_append, List.length_replicate]
        omega
      have hbdd :
          ∀ z ∈ negatives ++ (List.replicate remaining 0 ++ positives),
            -17 ≤ z ∧ z ≤ 17 := by
        intro z hz
        rcases List.mem_append.mp hz with hz' | hz'
        · exact hneg z hz'
        · rcases List.mem_append.mp hz' with hz'' | hz''
          · have := List.eq_of_mem_replicate hz''
            omega
          · exact hpos z hz''
      have hiff := a15_poly_fast_agree residue hres _ hlen' hbdd
      have hdec :
          decide (74 ≤ a15PolyEligibleCountReduced residue
              (negatives ++ (List.replicate remaining 0 ++ positives))) =
            decide (74 ≤ a15FastEligibleCountReduced residue
              (negatives ++ (List.replicate remaining 0 ++ positives))) := by
        simp only [decide_eq_decide]
        exact hiff
      simp only [List.append_assoc, hdec]
  | succ m ih =>
      intro remaining sum sq negatives positives hm hlen hneg hpos
      unfold a15PolyEnumerateByMagnitudeAux a15EnumerateByMagnitudeAux
      apply List.flatMap_congr
      intro negativeCount hnc
      have hnc' : negativeCount ≤ remaining := by
        have := List.mem_range.mp hnc
        omega
      apply List.flatMap_congr
      intro positiveCount hpc
      have hpc' : positiveCount ≤ remaining - negativeCount := by
        have hmem := List.mem_range.mp hpc
        by_cases hcase : (decide (residue = 2) && decide (m + 1 = 17)) = true
        · rw [if_pos hcase] at hmem
          omega
        · rw [if_neg hcase] at hmem
          omega
      by_cases hfeas :
          a15MagnitudeFeasible residue (m + 1)
              (remaining - (negativeCount + positiveCount))
              (sum + ((positiveCount : ℤ) - negativeCount) * ((m : ℤ) + 1))
              (sq + (negativeCount + positiveCount) * (m + 1) ^ 2) = true
      · simp only [hfeas, if_true]
        refine ih _ _ _ _ _ (by omega) ?_ ?_ ?_
        · simp only [List.length_append, List.length_replicate]
          omega
        · intro z hz
          rcases List.mem_append.mp hz with hz' | hz'
          · exact hneg z hz'
          · have := List.eq_of_mem_replicate hz'
            subst this
            omega
        · intro z hz
          rcases List.mem_append.mp hz with hz' | hz'
          · have := List.eq_of_mem_replicate hz'
            subst this
            omega
          · exact hpos z hz'
      · simp only [hfeas]
        simp

/-- Both residue branches of the search, with the generating-function
counter. -/
def a15PolyEnumeratedCandidateProfiles : List (Array ℤ) :=
  a15PolyEnumerateByMagnitudeAux 0 17 16 0 0 [] [] ++
    a15PolyEnumerateByMagnitudeAux 2 17 16 0 0 [] []

/-- The generating-function search emits exactly the profiles of the byte
histogram search. -/
theorem a15PolyEnumeratedCandidateProfiles_eq :
    a15PolyEnumeratedCandidateProfiles = a15EnumeratedCandidateProfiles :=
  congrArg₂ (· ++ ·)
    (a15PolyEnumerateByMagnitudeAux_eq 0 (Or.inl rfl) 17 16 0 0 [] []
      (by omega) (by simp) (by simp) (by simp))
    (a15PolyEnumerateByMagnitudeAux_eq 2 (Or.inr rfl) 17 16 0 0 [] []
      (by omega) (by simp) (by simp) (by simp))

end SRG266
