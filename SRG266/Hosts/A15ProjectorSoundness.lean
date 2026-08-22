/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.A15ProjectorSoundnessTheory
import SRG266.Hosts.A15ProjectorBridgeAudit

/-!
# Soundness of the generated A15 projector certificate aggregate

The reusable positive-semidefinite witness theory lives in
`A15ProjectorSoundnessTheory`.  This module adds the thirteen generated
profiles, their bounded audits, and the global survivor theorem.
-/

open scoped BigOperators Matrix

namespace SRG266

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- All generated profiles satisfy the structural shell-difference identity. -/
theorem a15ProjectorProfiles_standardAverage_checked :
    a15ProjectorProfileCertificates.all
      (fun certificate =>
        decide certificate.profile.standardAverageValid) = true := by
  rw [Array.all_eq_true_iff_forall_mem]
  intro certificate hcertificate
  apply decide_eq_true
  exact certificate.profile.standardAverageValid_of_bridgeValid
    (a15ProjectorProfile_bridgeValid certificate hcertificate)

theorem a15ProjectorProfile_standardAverageValid
    (certificate : A15ProjectorProfileCertificate)
    (hcertificate : certificate ∈ a15ProjectorProfileCertificates) :
    certificate.profile.standardAverageValid := by
  exact certificate.profile.standardAverageValid_of_bridgeValid
    (a15ProjectorProfile_bridgeValid certificate hcertificate)

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The direct shell multiplicities of a listed profile must be one of its
four globally surviving orbit-total vectors. -/
theorem A15ShellGramRealization.projectorOrbitTotals_mem_survivors
    (hG : IsHypothetical G) (x : V)
    (certificate : A15ProjectorProfileCertificate)
    (hcertificate : certificate ∈ a15ProjectorProfileCertificates)
    (realization :
      A15ShellGramRealization G x
        certificate.profile.centroidVector) :
    realization.projectorOrbitTotals G certificate.profile ∈
      certificate.survivors := by
  have hcheck : certificate.essentialCheck = true := by
    have hall :
        ∀ certificate ∈ a15ProjectorProfileCertificates,
          certificate.essentialCheck = true := by
      simpa only [Array.all_eq_true_iff_forall_mem] using
        a15ProjectorProfileCertificates_checked
    exact hall certificate hcertificate
  have hbridge :=
    a15ProjectorProfile_bridgeValid certificate hcertificate
  exact realization.projectorOrbitTotals_mem_survivors_of
    G hG x certificate hcheck hbridge
    (a15ProjectorRejection_bridgeCompatible certificate hcertificate)

end SRG266
