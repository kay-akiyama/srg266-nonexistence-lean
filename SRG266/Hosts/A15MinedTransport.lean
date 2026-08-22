/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Certificates.A15MinedScaledMatches00
import SRG266.Certificates.A15MinedScaledMatches01
import SRG266.Certificates.A15MinedScaledMatches02
import SRG266.Hosts.A15CentroidSolution
import SRG266.Hosts.A15FinalTransportSurvivors
import SRG266.Hosts.A15MinedProjectorConstantProfiles
import SRG266.Hosts.A15MinedProjectorProfile03
import SRG266.Hosts.A15MinedProjectorProfile04
import SRG266.Hosts.A15MinedProjectorProfile05
import SRG266.Hosts.A15MinedProjectorProfile06
import SRG266.Hosts.A15MinedProjectorProfile07
import SRG266.Hosts.A15MinedProjectorProfile09
import SRG266.Hosts.A15MinedProjectorProfile10
import SRG266.Hosts.A15MinedProfileData
import SRG266.Hosts.A15MinedUnsupportedProfiles

/-!
# Mined transport from 15 small A15 profiles

The divisibility theorem reduces the centroid sweep to 15 scaled
profiles.  Kernel computations identify thirteen of them with the projector
profiles used below.  The remaining two exceptional profiles are excluded by
exact Farkas separators.

Projector profiles 2, 9, and 11 are already excluded by mined class-difference
arguments, profile 4 by an aggregate class moment, and profile 6 by one
class-indicator quadratic form.  Profiles 5 and 7 use a class-moment lower
bound and the universal shell-multiplicity bound.  Profiles 3 and 10 use a
fixed class-indicator minor, while the four surviving profiles use the
constructive final transport.
Thus this route imports neither the 2,199 rejected centroid certificates nor
the 731-chunk exact-enumeration audit nor the nine projector
certificate payloads.
-/

namespace SRG266

set_option maxRecDepth 100000
set_option maxHeartbeats 0

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem a15MinedExceptionalRealization_elim
    (hG : IsHypothetical G) (x : V)
    (coordinates : List ℤ)
    (realization :
      A15ShellGramRealization G x (a15SmallProfile coordinates))
    (i : Fin a15MinedExceptionalCertificates.length)
    (hprofile :
      a15SmallProfile coordinates =
        (a15MinedExceptionalCertificates.get i).toCertificate.d) :
    Nonempty (A15FinalShellCase G x) := by
  let certificate := a15MinedExceptionalCertificates.get i
  have hcertificate : certificate ∈ a15MinedExceptionalCertificates :=
    by
      change a15MinedExceptionalCertificates.get i ∈
        a15MinedExceptionalCertificates
      exact List.get_mem a15MinedExceptionalCertificates i
  have hcheck : certificate.fastCheck = true :=
    (List.all_eq_true.mp a15MinedExceptionalCertificates_checked)
      certificate hcertificate
  have hbounded :=
    (hprofile ▸ realization).exists_centroid_bounded_solution G hG x
  exact (certificate.no_bounded_solution_of_fastCheck hcheck hbounded).elim

/-- Every realization of one of the 15 mined profiles reaches a final shell
case.  Four cases use the constructive survivor transport, nine projector
profiles are impossible, and the other two contradict their checked
bounded-solution separators. -/
theorem a15MinedRealization_hasFinalShellCase
    (hG : IsHypothetical G) (x : V)
    (coordinates : List ℤ)
    (hcoordinates : coordinates ∈ a15MinedCandidateProfiles)
    (realization :
      A15ShellGramRealization G x (a15SmallProfile coordinates)) :
    Nonempty (A15FinalShellCase G x) := by
  simp only [a15MinedCandidateProfiles, List.mem_cons, List.not_mem_nil,
    or_false] at hcoordinates
  rcases hcoordinates with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact a15MinedExceptionalRealization_elim G hG x _ realization
      ⟨1, by decide⟩ a15MinedNormProfile00_exceptional01
  · exact (a15MinedNormProfile02_projector12 ▸ realization).profile12_hasFinalShellCase
      G hG x
  · exact (a15MinedNormProfile03_no_realization G hG x realization).elim
  · exact (a15MinedNormProfile04_no_realization G hG x realization).elim
  · exact (a15MinedNormProfile05_no_realization G hG x realization).elim
  · exact (a15MinedNormProfile06_projector08 ▸ realization).profile08_hasFinalShellCase
      G hG x
  · exact (a15MinedNormProfile07_no_realization G hG x realization).elim
  · exact (a15MinedNormProfile08_no_realization G hG x realization).elim
  · exact (a15MinedNormProfile09_no_realization G hG x realization).elim
  · exact (a15MinedNormProfile11_no_realization G hG x realization).elim
  · exact (a15MinedNormProfile12_no_realization G hG x realization).elim
  · exact (a15MinedNormProfile13_no_realization G hG x realization).elim
  · exact (a15MinedNormProfile14_projector01 ▸ realization).profile01_hasFinalShellCase
      G hG x
  · exact a15MinedExceptionalRealization_elim G hG x _ realization
      ⟨0, by decide⟩ a15MinedNormProfile15_exceptional00
  · exact (a15MinedNormProfile16_projector00 ▸ realization).profile00_hasFinalShellCase
      G hG x

private theorem a15MinedNormProfile_mem_candidate_of_ne
    (coordinates : List ℤ)
    (hnorm : coordinates ∈ a15MinedNormProfiles)
    (hne01 : coordinates ≠ a15MinedNormProfile01)
    (hne10 : coordinates ≠ a15MinedNormProfile10) :
    coordinates ∈ a15MinedCandidateProfiles := by
  simpa [a15MinedNormProfiles, a15MinedCandidateProfiles, hne01, hne10]
    using hnorm

/-- A realization of any of the 17 mined norm profiles reaches the final
transport.  The two profiles outside the 15-profile support list have no
eligible four-subsets at all. -/
theorem a15MinedNormRealization_hasFinalShellCase
    (hG : IsHypothetical G) (x : V)
    (coordinates : List ℤ)
    (hcoordinates : coordinates ∈ a15MinedNormProfiles)
    (realization :
      A15ShellGramRealization G x (a15SmallProfile coordinates)) :
    Nonempty (A15FinalShellCase G x) := by
  have hne01 : coordinates ≠ a15MinedNormProfile01 := by
    intro hcoordinates01
    subst coordinates
    exact a15MinedNormProfile01_no_realization G hG x realization
  have hne10 : coordinates ≠ a15MinedNormProfile10 := by
    intro hcoordinates10
    subst coordinates
    exact a15MinedNormProfile10_no_realization G hG x realization
  exact a15MinedRealization_hasFinalShellCase G hG x coordinates
    (a15MinedNormProfile_mem_candidate_of_ne
      coordinates hcoordinates hne01 hne10)
    realization

end SRG266
