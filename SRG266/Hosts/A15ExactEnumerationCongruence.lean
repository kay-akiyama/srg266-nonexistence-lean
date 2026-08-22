/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.A15FastCountCorrect

/-!
# The reference and fast A15 enumerators emit the same profiles

`a15ExactEnumerateByMagnitudeAux` and `a15EnumerateByMagnitudeAux` are the
same recursion: identical branching on the magnitude multiplicities, identical
feasibility pruning, identical terminal sum and squared-norm tests.  They
differ in exactly one token, the eligible-shell counter queried against the
threshold `74` at a complete profile.

`a15_counters_agree` says those two counters answer the threshold question
identically on bounded length-sixteen reduced profiles.  A structural
induction on the magnitude parameter therefore identifies the two searches
outright, with no evaluation at all: the invariant to carry is that the
partial profile always has sixteen slots and coordinates bounded by
seventeen, which the recursion preserves because it only ever appends `±m`
with `m ≤ 17`.
-/

namespace SRG266

set_option maxRecDepth 100000

/-- The two magnitude recursions coincide on every reachable state. -/
theorem a15ExactEnumerateByMagnitudeAux_eq (residue : ℤ)
    (hres : residue = 0 ∨ residue = 2) :
    ∀ (m remaining : ℕ) (sum : ℤ) (sq : ℕ) (negatives positives : List ℤ),
      m ≤ 17 →
      negatives.length + remaining + positives.length = 16 →
      (∀ z ∈ negatives, -17 ≤ z ∧ z ≤ 17) →
      (∀ z ∈ positives, -17 ≤ z ∧ z ≤ 17) →
      a15ExactEnumerateByMagnitudeAux residue m remaining sum sq negatives
          positives =
        a15EnumerateByMagnitudeAux residue m remaining sum sq negatives
          positives := by
  intro m
  induction m with
  | zero =>
      intro remaining sum sq negatives positives _ hlen hneg hpos
      unfold a15ExactEnumerateByMagnitudeAux a15EnumerateByMagnitudeAux
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
      have hiff := a15_counters_agree residue hres _ hlen' hbdd
      have hdec :
          decide (74 ≤ a15ExactEligibleCardReduced residue
              (negatives ++ (List.replicate remaining 0 ++ positives))) =
            decide (74 ≤ a15FastEligibleCountReduced residue
              (negatives ++ (List.replicate remaining 0 ++ positives))) := by
        simp only [decide_eq_decide]
        exact hiff
      simp only [List.append_assoc, hdec]
  | succ m ih =>
      intro remaining sum sq negatives positives hm hlen hneg hpos
      unfold a15ExactEnumerateByMagnitudeAux a15EnumerateByMagnitudeAux
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

/-- The reference and fast A15 centroid searches emit the same profile
list. -/
theorem a15ExactEnumeratedCandidateProfiles_eq :
    a15ExactEnumeratedCandidateProfiles = a15EnumeratedCandidateProfiles :=
  congrArg₂ (· ++ ·)
    (a15ExactEnumerateByMagnitudeAux_eq 0 (Or.inl rfl) 17 16 0 0 [] []
      (by omega) (by simp) (by simp) (by simp))
    (a15ExactEnumerateByMagnitudeAux_eq 2 (Or.inr rfl) 17 16 0 0 [] []
      (by omega) (by simp) (by simp) (by simp))

end SRG266
