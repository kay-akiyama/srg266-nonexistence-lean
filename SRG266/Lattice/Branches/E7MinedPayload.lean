/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Certificates.E7MinedPairData
import SRG266.Hosts.E7CentroidTransport
import SRG266.Hosts.E7MinedProfile
import SRG266.Lattice.Branches.E7PayloadData

/-!
# The mined E7 branch payload

This module carries an E7 branch payload through the bounded 25-profile
search, the checked Weyl paths, and the five canonical residual types.  Its
construction from lattice data remains in `SRG266.Lattice.Branches.E7E7`.
-/

namespace SRG266
namespace Lattice

open scoped BigOperators

universe u

set_option maxRecDepth 40000

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The left half of every branch payload is one of the 25 mined profiles,
up to the coordinate permutation constituting its elementary Weyl action. -/
theorem E7BranchPayload.left_factors_through_mined
    {x : V} (P : E7BranchPayload G x) :
    ∃ coordinates ∈ e7MinedComponentProfiles,
      (coordinates.map fun z => 5 * z).Perm
        (List.ofFn (e7ComponentEnumerationProfile P.left)) := by
  obtain ⟨hfive, n, hn, hsq⟩ := P.left_mined
  exact e7Profile_factors_through_mined
    (e7ComponentEnumerationProfile P.left) hfive P.left_sum
    n hn hsq P.left_parity

/-- The corresponding 25-profile factorization of the right half. -/
theorem E7BranchPayload.right_factors_through_mined
    {x : V} (P : E7BranchPayload G x) :
    ∃ coordinates ∈ e7MinedComponentProfiles,
      (coordinates.map fun z => 5 * z).Perm
        (List.ofFn (e7ComponentEnumerationProfile P.right)) := by
  obtain ⟨hfive, n, hn, hsq⟩ := P.right_mined
  exact e7Profile_factors_through_mined
    (e7ComponentEnumerationProfile P.right) hfive P.right_sum
    n hn hsq P.right_parity

/-- Canonical ordering upgrades the left factorization from permutation to
literal equality. -/
theorem E7BranchPayload.left_eq_mined
    {x : V} (P : E7BranchPayload G x) :
    ∃ coordinates ∈ e7MinedComponentProfiles,
      coordinates.map (fun z => 5 * z) =
        List.ofFn (e7ComponentEnumerationProfile P.left) := by
  obtain ⟨coordinates, hcoordinates, hperm⟩ :=
    P.left_factors_through_mined G
  have hsource := e7MinedComponentProfiles_pairwise coordinates hcoordinates
  have hscaled :
      (coordinates.map fun z => 5 * z).Pairwise (· ≤ ·) :=
    hsource.map _ (fun _ _ h => by omega)
  exact ⟨coordinates, hcoordinates,
    List.Perm.eq_of_pairwise' hscaled P.left_sorted hperm⟩

/-- Literal equality for the canonically ordered right component. -/
theorem E7BranchPayload.right_eq_mined
    {x : V} (P : E7BranchPayload G x) :
    ∃ coordinates ∈ e7MinedComponentProfiles,
      coordinates.map (fun z => 5 * z) =
        List.ofFn (e7ComponentEnumerationProfile P.right) := by
  obtain ⟨coordinates, hcoordinates, hperm⟩ :=
    P.right_factors_through_mined G
  have hsource := e7MinedComponentProfiles_pairwise coordinates hcoordinates
  have hscaled :
      (coordinates.map fun z => 5 * z).Pairwise (· ≤ ·) :=
    hsource.map _ (fun _ _ h => by omega)
  exact ⟨coordinates, hcoordinates,
    List.Perm.eq_of_pairwise' hscaled P.right_sorted hperm⟩

/-- The left component continues from the 25-profile factorization to one of
the seven checked Weyl-canonical representatives. -/
theorem E7BranchPayload.left_has_minedWeylCertificate
    {x : V} (P : E7BranchPayload G x) :
    ∃ coordinates c,
      coordinates ∈ e7MinedComponentProfiles ∧
      coordinates.map (fun z => 5 * z) =
        List.ofFn (e7ComponentEnumerationProfile P.left) ∧
      c ∈ e7MinedWeylCertificates ∧
      List.ofFn c.profile = coordinates ∧ c.Valid := by
  obtain ⟨coordinates, hcoordinates, hperm⟩ :=
    P.left_eq_mined G
  obtain ⟨c, hc, hprofile, hvalid⟩ :=
    e7MinedProfile_hasWeylCertificate coordinates hcoordinates
  exact ⟨coordinates, c, hcoordinates, hperm, hc, hprofile, hvalid⟩

/-- The analogous seven-representative certificate for the right component. -/
theorem E7BranchPayload.right_has_minedWeylCertificate
    {x : V} (P : E7BranchPayload G x) :
    ∃ coordinates c,
      coordinates ∈ e7MinedComponentProfiles ∧
      coordinates.map (fun z => 5 * z) =
        List.ofFn (e7ComponentEnumerationProfile P.right) ∧
      c ∈ e7MinedWeylCertificates ∧
      List.ofFn c.profile = coordinates ∧ c.Valid := by
  obtain ⟨coordinates, hcoordinates, hperm⟩ :=
    P.right_eq_mined G
  obtain ⟨c, hc, hprofile, hvalid⟩ :=
    e7MinedProfile_hasWeylCertificate coordinates hcoordinates
  exact ⟨coordinates, c, hcoordinates, hperm, hc, hprofile, hvalid⟩

/-- The mined component and Weyl certificates transport a branch payload to
one of the five canonical residual E7 realizations.  The proof uses neither
the scalar-DP audit nor the 956-profile concrete enumeration audit. -/
theorem E7BranchPayload.has_minedCanonicalRealization
    (hG : IsHypothetical G) (x : V) (P : E7BranchPayload G x) :
    ∃ kind : E7ResidualType,
      Nonempty
        (E7ShellGramRealization G x
          (e7ResidualCanonical kind).1 (e7ResidualCanonical kind).2) := by
  obtain ⟨leftCoordinates, leftCertificate, _, hleftScaled,
      hleftCertificate, hleftProfile, hleftValid⟩ :=
    P.left_has_minedWeylCertificate G
  obtain ⟨rightCoordinates, rightCertificate, _, hrightScaled,
      hrightCertificate, hrightProfile, hrightValid⟩ :=
    P.right_has_minedWeylCertificate G
  have hleftScale :
      (fun i => 5 * leftCertificate.profile i) =
        e7ComponentEnumerationProfile P.left := by
    have hscaled := hleftScaled
    rw [← hleftProfile, List.map_ofFn] at hscaled
    have hfunctions := List.ofFn_inj.mp hscaled
    funext i
    simpa only [Function.comp_apply] using congrFun hfunctions i
  have hrightScale :
      (fun i => 5 * rightCertificate.profile i) =
        e7ComponentEnumerationProfile P.right := by
    have hscaled := hrightScaled
    rw [← hrightProfile, List.map_ofFn] at hscaled
    have hfunctions := List.ofFn_inj.mp hscaled
    funext i
    simpa only [Function.comp_apply] using congrFun hfunctions i
  have hleftDiv :
      (fun i => e7ComponentEnumerationProfile P.left i / 5) =
        leftCertificate.profile := by
    funext i
    have hi := congrFun hleftScale i
    rw [← hi]
    omega
  have hrightDiv :
      (fun i => e7ComponentEnumerationProfile P.right i / 5) =
        rightCertificate.profile := by
    funext i
    have hi := congrFun hrightScale i
    rw [← hi]
    omega
  have hleftDivisible : ∀ i,
      e7ComponentEnumerationProfile P.left i % 5 = 0 := by
    intro i
    exact Int.dvd_iff_emod_eq_zero.mp (P.left_mined.1 i)
  have hrightDivisible : ∀ i,
      e7ComponentEnumerationProfile P.right i % 5 = 0 := by
    intro i
    exact Int.dvd_iff_emod_eq_zero.mp (P.right_mined.1 i)
  have hleftEvaluation : ∀ w : E7WeightIndex,
      integerDot
          (fun i => e7ComponentEnumerationProfile P.left i / 5)
          (e7Weight4 w) % 8 = 0 := by
    rw [hleftDiv]
    exact hleftValid.2.2.2.2
  have hrightEvaluation : ∀ w : E7WeightIndex,
      integerDot
          (fun i => e7ComponentEnumerationProfile P.right i / 5)
          (e7Weight4 w) % 8 = 0 := by
    rw [hrightDiv]
    exact hrightValid.2.2.2.2
  have source :
      E7ShellGramRealization G x
        leftCertificate.profile rightCertificate.profile := by
    simpa only [hleftDiv, hrightDiv] using
      P.realization.toResidualOfFactorAudits G
        hleftDivisible hrightDivisible hleftEvaluation hrightEvaluation
  obtain ⟨leftTarget⟩ := source.nonempty_reflectLeftList G
    leftCertificate.reflections hleftValid.2.2.2.1 hleftValid.2.2.1
  obtain ⟨target⟩ := leftTarget.nonempty_reflectRightList G
    rightCertificate.reflections hrightValid.2.2.2.1 hrightValid.2.2.1
  have hleftSq :
      (∑ i, (e7ComponentEnumerationProfile P.left i) ^ 2) =
        25 * ∑ i, (leftCertificate.profile i) ^ 2 := by
    calc
      _ = ∑ i, (5 * leftCertificate.profile i) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← congrFun hleftScale i]
      _ = 25 * ∑ i, (leftCertificate.profile i) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hrightSq :
      (∑ i, (e7ComponentEnumerationProfile P.right i) ^ 2) =
        25 * ∑ i, (rightCertificate.profile i) ^ 2 := by
    calc
      _ = ∑ i, (5 * rightCertificate.profile i) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← congrFun hrightScale i]
      _ = 25 * ∑ i, (rightCertificate.profile i) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have htotalSq := P.realization.profile_sq_sum G hG x
  rw [hleftSq, hrightSq] at htotalSq
  simp only [pow_two] at htotalSq
  have hnorm :
      e7MinedProfileSq (List.ofFn leftCertificate.profile) +
        e7MinedProfileSq (List.ofFn rightCertificate.profile) = 48 := by
    simp only [e7MinedProfileSq, List.map_ofFn, List.sum_ofFn,
      Function.comp_apply]
    omega
  have heligible :
      74 ≤ Fintype.card
        (E7ResidualEligibleIndex
          leftCertificate.target rightCertificate.target) :=
    target.seventyFour_le_eligible_card G hG x
  obtain ⟨kind, horientation⟩ :=
    e7MinedWeylCertificates_pair_residual
      leftCertificate rightCertificate
      hleftCertificate hrightCertificate hleftValid hrightValid
      hnorm heligible
  refine ⟨kind, ?_⟩
  rcases horientation with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
  · simpa only [hleft, hright] using Nonempty.intro target
  · simpa only [hleft, hright] using Nonempty.intro (target.swap G)

/-- The E7 branch is closed by the 25-profile mined search, seven checked
Weyl representatives, and five canonical residual contradictions. -/
theorem E7BranchPayload.elim
    (hG : IsHypothetical G) (x : V) (P : E7BranchPayload G x) : False := by
  obtain ⟨kind, ⟨realization⟩⟩ := P.has_minedCanonicalRealization G hG x
  exact (no_e7ResidualCanonical_realization G hG x kind).false realization

end Lattice
end SRG266
