/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.A15ExactEnumerationSoundness
import SRG266.Certificates.A15ExactEnumerationData
import SRG266.Hosts.A15CentroidTransport

/-!
# Assembly of the complete A15 canonical enumeration

The declarative reference enumerator is structurally complete for every
bounded canonical reduced profile.  An explicit finite-enumeration input
identifies its output set with the fast enumerator, whose profiles are already
transported through all centroid and projector certificates.
-/

namespace SRG266

set_option maxRecDepth 100000

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [A15CentroidEnumerationInput] [A15ExactEnumerationInput]

/-- Membership in the declarative reference enumeration suffices for the
already checked post-enumeration A15 transport. -/
theorem a15ExactEnumeratedRealization_hasFinalShellCase
    (hG : IsHypothetical G) (x : V)
    (d : Array ℤ) (hd : d ∈ a15ExactEnumeratedCandidateProfiles)
    (realization :
      A15ShellGramRealization G x (a15EnumerationProfile d)) :
    Nonempty (A15FinalShellCase G x) := by
  have hdFinset :
      d ∈ a15ExactEnumeratedCandidateProfiles.toFinset := by
    simpa using hd
  rw [a15ExactEnumeratedCandidateProfiles_eq_fast] at hdFinset
  have hdFast : d ∈ a15EnumeratedCandidateProfiles := by
    simpa using hdFinset
  exact
    a15EnumeratedRealization_hasFinalShellCase
      G hG x d hdFast realization

/-- Every normalized reduced A15 realization satisfying the elementary
centroid invariants reaches one of the four final shell cases.

The input coordinates need not themselves be sorted: their count-based
canonical reconstruction is used both by the realization and by the
enumerator. -/
theorem a15CanonicalRealization_hasFinalShellCase
    (hG : IsHypothetical G) (x : V)
    (residue : ℤ) (coordinates : List ℤ)
    (hresidue : residue = 0 ∨ residue = 2)
    (hlength : coordinates.length = 16)
    (hbounds : ∀ z ∈ coordinates, -17 ≤ z ∧ z ≤ 17)
    (hsum : coordinates.sum = a15ReducedTargetSum residue)
    (hsq :
      (coordinates.map (fun z : ℤ => z * z)).sum =
        a15ReducedTargetSq residue)
    (hspecial : residue = 2 → coordinates.count 17 = 0)
    (realization :
      A15ShellGramRealization G x
        (a15EnumerationProfile
          (a15ScaleReducedProfile residue
            (a15CanonicalReducedCoordinates coordinates)))) :
    Nonempty (A15FinalShellCase G x) := by
  let canonical := a15CanonicalReducedCoordinates coordinates
  have hperm :=
    a15CanonicalReducedCoordinates_perm coordinates hbounds
  have hcanonicalLength : canonical.length = 16 := by
    exact hperm.length_eq.trans hlength
  have heligibleCard :
      74 ≤
        Fintype.card
          (A15EligibleIndex
            (a15EnumerationProfile
              (a15ScaleReducedProfile residue canonical))) :=
    realization.seventyFour_le_eligible_card G hG x
  have heligibleExact :
      74 ≤ a15ExactEligibleCardReduced residue canonical := by
    rw [a15ExactEligibleCardReduced_eq_card
      residue canonical hcanonicalLength]
    exact heligibleCard
  have hmem :
      a15ScaleReducedProfile residue canonical ∈
        a15ExactEnumeratedCandidateProfiles := by
    have hbranch :=
      a15_canonical_reduced_profile_mem_exact_enumeration
        residue coordinates hlength hbounds hsum hsq hspecial
        (by simpa only [canonical] using heligibleExact)
    rcases hresidue with hresidueZero | hresidueTwo
    · apply List.mem_append.mpr
      left
      simpa only [hresidueZero] using hbranch
    ·
      apply List.mem_append.mpr
      right
      simpa only [hresidueTwo] using hbranch
  exact
    a15ExactEnumeratedRealization_hasFinalShellCase
      G hG x (a15ScaleReducedProfile residue canonical)
      hmem realization

end SRG266
