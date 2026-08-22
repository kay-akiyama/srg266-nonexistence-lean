/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.A15FinalTransport
import SRG266.Hosts.A15CentroidSolution
import SRG266.Certificates.A15CentroidData
import SRG266.Certificates.A15CentroidEnumerationData
import SRG266.Certificates.A15ProjectorData

/-!
# Transport through the A15 centroid certificates

A direct shell realization assigns multiplicities to the eligible
four-subsets.  This module proves that those multiplicities form exactly the
bounded integer solution excluded by each centroid Farkas certificate.
Consequently, any listed direct realization must belong to the 13 projector
profiles, where `A15FinalTransport` finishes the reduction.
-/

open scoped BigOperators Matrix

namespace SRG266

set_option maxRecDepth 100000
set_option maxHeartbeats 0

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

set_option maxRecDepth 100000 in
/-- Alignment of the 13 projector profiles with the centroid-survivor
list.  It lives at the transport layer so the projector data does not
imports all 2,199 rejected centroid certificates. -/
theorem a15ProjectorCentroids_match :
    (a15ProjectorProfileCertificates.toList.map
      (fun certificate => certificate.profile.d)) =
    (a15GeneratedCentroidSurvivors.map
      (fun survivor => survivor.d)) := by
  rfl

/-- Any direct realization whose centroid array occurs in the checked list
survives to one of the four final A15 shell cases. -/
theorem a15ListedRealization_hasFinalShellCase
    (hG : IsHypothetical G) (x : V)
    (d : Array ℤ) (hd : d ∈ a15ListedCandidateProfiles)
    (realization :
      A15ShellGramRealization G x (a15EnumerationProfile d)) :
    Nonempty (A15FinalShellCase G x) := by
  have hd' :
      d ∈ List.map (fun certificate => certificate.d)
          a15GeneratedCentroidCertificates ∨
        d ∈ List.map (fun survivor => survivor.d)
          a15GeneratedCentroidSurvivors := by
    simpa [a15ListedCandidateProfiles] using hd
  rcases hd' with hrejected | hsurvivor
  · obtain ⟨certificate, hcertificate, rfl⟩ :=
      List.mem_map.mp hrejected
    have hbounded :=
      realization.exists_centroid_bounded_solution G hG x
    exact
      (a15_generated_centroid_certificate_no_bounded_solution
        certificate hcertificate hbounded).elim
  · have hprojector :
        d ∈
          a15ProjectorProfileCertificates.toList.map
            (fun certificate => certificate.profile.d) := by
      rw [a15ProjectorCentroids_match]
      exact hsurvivor
    obtain ⟨certificate, hcertificate, hcertificateD⟩ :=
      List.mem_map.mp hprojector
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hcertificate
    let i : Fin a15ProjectorProfileCertificates.size :=
      ⟨j.1, by exact j.2⟩
    have hcertificateEq :
        a15ProjectorProfileCertificates[i] = certificate := by
      simpa [i] using hj
    have hdEq :
        a15ProjectorProfileCertificates[i].profile.d = d := by
      rw [hcertificateEq]
      exact hcertificateD
    have hvector :
        a15EnumerationProfile d =
          a15ProjectorProfileCertificates[i].profile.centroidVector := by
      funext k
      change
        d.getD k.1 0 =
          a15ProjectorProfileCertificates[i].profile.d.getD k.1 0
      rw [hdEq]
    exact
      (hvector ▸ realization).hasFinalShellCase G hG x i

/-- The supplied centroid-enumeration equality, together with the
checked separator and projector layers, transports every generated direct
realization to a final shell case. -/
theorem a15EnumeratedRealization_hasFinalShellCase
    [A15CentroidEnumerationInput]
    (hG : IsHypothetical G) (x : V)
    (d : Array ℤ) (hd : d ∈ a15EnumeratedCandidateProfiles)
    (realization :
      A15ShellGramRealization G x (a15EnumerationProfile d)) :
    Nonempty (A15FinalShellCase G x) := by
  have hdFinset : d ∈ a15EnumeratedCandidateProfiles.toFinset := by
    simpa using hd
  rw [a15EnumeratedCandidateProfiles_eq_listed] at hdFinset
  have hdListed : d ∈ a15ListedCandidateProfiles := by
    simpa using hdFinset
  exact
    a15ListedRealization_hasFinalShellCase
      G hG x d hdListed realization

end SRG266
