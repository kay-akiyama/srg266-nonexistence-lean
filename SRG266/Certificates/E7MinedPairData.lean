/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Certificates.E7MinedWeylAudit
import SRG266.Certificates.E7MinedExcludedPairCount
import Mathlib.Data.List.GetD

/-!
# Checked compression of the seven E7 component orbits to five pair types

The lattice branch fixes the sum of the two divided squared norms to `48`.
Among the resulting six unordered pairs of the seven Weyl representatives,
the special-six/special-six pair has no eligible shell columns.  The other
five pairs are exactly `E7ResidualType`.

This is a 49-pair computation, independent of the 956-profile and
54-survivor sweeps.
-/

namespace SRG266

def e7MinedProfileSq (profile : List ℤ) : ℤ :=
  (profile.map fun z => z * z).sum

def e7MinedScaledProfile (profile : List ℤ) : Fin 8 → ℤ :=
  fun i => 5 * profile.getD i.1 0

def e7MinedWeylNormComplementaryPairs : List (List ℤ × List ℤ) :=
  (e7MinedWeylCanonicalProfiles.flatMap fun left =>
    e7MinedWeylCanonicalProfiles.map fun right => (left, right)).filter
      fun pair => decide
        (e7MinedProfileSq pair.1 + e7MinedProfileSq pair.2 = 48)

def e7ResidualTypes : List E7ResidualType :=
  [ .twoTen, .fourEightGeneric, .fourEightSpecial,
    .sixGenericSixGeneric, .sixGenericSixSpecial ]

def e7ResidualCanonicalListPair
    (kind : E7ResidualType) : List ℤ × List ℤ :=
  (List.ofFn (e7ResidualCanonical kind).1,
    List.ofFn (e7ResidualCanonical kind).2)

/-- Both orientations are retained so that this list can classify an ordered
pair without imposing a convention on the two E7 factors. -/
def e7MinedResidualOrderedPairs : List (List ℤ × List ℤ) :=
  e7ResidualTypes.flatMap fun kind =>
    let pair := e7ResidualCanonicalListPair kind
    [pair, (pair.2, pair.1)]

def e7MinedNormComplementaryOrderedPairs : List (List ℤ × List ℤ) :=
  e7MinedResidualOrderedPairs ++ [e7MinedExcludedSixSpecialPair]

/-- Squared-norm complementarity cuts the 49 ordered pairs down to the five
residual types and one exceptional special-six/special-six pair. -/
theorem e7MinedWeylNormComplementaryPairs_eq_candidates :
    e7MinedWeylNormComplementaryPairs.toFinset =
      e7MinedNormComplementaryOrderedPairs.toFinset := by
  decide +kernel

/-- Every serialized Weyl path preserves the component squared norm. -/
theorem E7MinedWeylCertificate.profileSq_eq_targetSq
    (c : E7MinedWeylCertificate)
    (hc : c ∈ e7MinedWeylCertificates) :
    e7MinedProfileSq (List.ofFn c.profile) =
      e7MinedProfileSq (List.ofFn c.target) := by
  have hall :
      e7MinedWeylCertificates.all (fun certificate => decide
        (e7MinedProfileSq (List.ofFn certificate.profile) =
          e7MinedProfileSq (List.ofFn certificate.target))) = true := by
    decide +kernel
  exact of_decide_eq_true ((List.all_eq_true.mp hall) c hc)

theorem e7MinedWeylPair_mem_residual
    (left right : List ℤ)
    (hleft : left ∈ e7MinedWeylCanonicalProfiles)
    (hright : right ∈ e7MinedWeylCanonicalProfiles)
    (hnorm : e7MinedProfileSq left + e7MinedProfileSq right = 48)
    (heligible : 74 ≤ e7MinedPairEligibleCount (left, right)) :
    (left, right) ∈ e7MinedResidualOrderedPairs := by
  have hcomplementary :
      (left, right) ∈ e7MinedWeylNormComplementaryPairs := by
    simp only [e7MinedWeylNormComplementaryPairs, List.mem_filter,
      List.mem_flatMap, List.mem_map, decide_eq_true_eq]
    exact ⟨⟨left, hleft, right, hright, rfl⟩, hnorm⟩
  have hfin :
      (left, right) ∈ e7MinedWeylNormComplementaryPairs.toFinset :=
    List.mem_toFinset.mpr hcomplementary
  rw [e7MinedWeylNormComplementaryPairs_eq_candidates] at hfin
  have hcandidates :
      (left, right) ∈ e7MinedNormComplementaryOrderedPairs :=
    List.mem_toFinset.mp hfin
  simp only [e7MinedNormComplementaryOrderedPairs, List.mem_append,
    List.mem_singleton] at hcandidates
  rcases hcandidates with hresidual | hexcluded
  · exact hresidual
  · rw [hexcluded, e7MinedExcludedSixSpecialPair_eligibleCount] at heligible
    omega

/-- Declarative form of membership in the ten oriented entries: a residual
type exists and the pair is its canonical orientation or its swap. -/
theorem e7MinedResidualOrderedPairs_spec
    (pair : List ℤ × List ℤ)
    (hpair : pair ∈ e7MinedResidualOrderedPairs) :
    ∃ kind ∈ e7ResidualTypes,
      pair = e7ResidualCanonicalListPair kind ∨
        pair = ((e7ResidualCanonicalListPair kind).2,
          (e7ResidualCanonicalListPair kind).1) := by
  simp only [e7MinedResidualOrderedPairs, List.mem_flatMap] at hpair
  obtain ⟨kind, hkind, hpair⟩ := hpair
  refine ⟨kind, hkind, ?_⟩
  simpa only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] using hpair

/-- Certificate-level classification.  Once a pair of checked paths has
complementary source norm and at least 74 target shell columns, its endpoints
are one of the five canonical residual pairs, with a possible factor swap. -/
theorem e7MinedWeylCertificates_pair_residual
    (left right : E7MinedWeylCertificate)
    (hleft : left ∈ e7MinedWeylCertificates)
    (hright : right ∈ e7MinedWeylCertificates)
    (vleft : left.Valid) (vright : right.Valid)
    (hnorm :
      e7MinedProfileSq (List.ofFn left.profile) +
        e7MinedProfileSq (List.ofFn right.profile) = 48)
    (heligible :
      74 ≤ Fintype.card
        (E7ResidualEligibleIndex left.target right.target)) :
    ∃ kind : E7ResidualType,
      (left.target = (e7ResidualCanonical kind).1 ∧
        right.target = (e7ResidualCanonical kind).2) ∨
      (left.target = (e7ResidualCanonical kind).2 ∧
        right.target = (e7ResidualCanonical kind).1) := by
  have htargetNorm :
      e7MinedProfileSq (List.ofFn left.target) +
        e7MinedProfileSq (List.ofFn right.target) = 48 := by
    rw [← left.profileSq_eq_targetSq hleft,
      ← right.profileSq_eq_targetSq hright]
    exact hnorm
  have heligibleLists :
      74 ≤ e7MinedPairEligibleCount
        (List.ofFn left.target, List.ofFn right.target) := by
    have hleftFn :
        (fun i : Fin 8 => (List.ofFn left.target).getD i.1 0) =
          left.target := by
      funext i
      rw [List.getD_eq_getElem _ 0 (by simp), List.getElem_ofFn]
    have hrightFn :
        (fun i : Fin 8 => (List.ofFn right.target).getD i.1 0) =
          right.target := by
      funext i
      rw [List.getD_eq_getElem _ 0 (by simp), List.getElem_ofFn]
    simpa only [e7MinedPairEligibleCount, hleftFn, hrightFn] using heligible
  have hpair := e7MinedWeylPair_mem_residual
    (List.ofFn left.target) (List.ofFn right.target)
    vleft.2.1 vright.2.1 htargetNorm heligibleLists
  obtain ⟨kind, _, horientation⟩ :=
    e7MinedResidualOrderedPairs_spec _ hpair
  refine ⟨kind, ?_⟩
  rcases horientation with horientation | horientation
  · left
    have h₁ := congrArg Prod.fst horientation
    have h₂ := congrArg Prod.snd horientation
    simp only [e7ResidualCanonicalListPair] at h₁ h₂
    exact ⟨List.ofFn_inj.mp h₁, List.ofFn_inj.mp h₂⟩
  · right
    have h₁ := congrArg Prod.fst horientation
    have h₂ := congrArg Prod.snd horientation
    simp only [e7ResidualCanonicalListPair] at h₁ h₂
    exact ⟨List.ofFn_inj.mp h₁, List.ofFn_inj.mp h₂⟩

end SRG266
