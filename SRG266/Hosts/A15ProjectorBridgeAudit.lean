/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Certificates.A15ProjectorData
import SRG266.Hosts.A15QuickBridge

/-!
# Audited bridge facts for the generated A15 projector profiles

The witness-shape checks are evaluated in bounded generated chunks. Their
generic soundness theorem turns the checked shapes into the full bilinear
compatibility needed by the direct-shell argument.

The compact orbit-membership certificates list only eligible four-subsets.
Their generic soundness theorem obtains coverage from the independently
checked eligible-shell cardinality, so no whole-universe native evaluation is
needed here.
-/

namespace SRG266

set_option maxRecDepth 100000
theorem a15ProjectorProfile_bridgeValid
    (certificate : A15ProjectorProfileCertificate)
    (hcertificate : certificate ∈ a15ProjectorProfileCertificates) :
    certificate.profile.bridgeValid := by
  simp [a15ProjectorProfileCertificates, Array.mem_def] at hcertificate
  rcases hcertificate with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact a15ProjectorProfile00BridgeCertificate.bridgeValid
      a15ProjectorProfile00_membership_valid
      (of_decide_eq_true a15ProjectorProfile00_bridgeStatic_checked)
  · exact a15ProjectorProfile01BridgeCertificate.bridgeValid
      a15ProjectorProfile01_membership_valid
      (of_decide_eq_true a15ProjectorProfile01_bridgeStatic_checked)
  · exact a15ProjectorProfile02BridgeCertificate.bridgeValid
      a15ProjectorProfile02_membership_valid
      (of_decide_eq_true a15ProjectorProfile02_bridgeStatic_checked)
  · exact a15ProjectorProfile03BridgeCertificate.bridgeValid
      a15ProjectorProfile03_membership_valid
      (of_decide_eq_true a15ProjectorProfile03_bridgeStatic_checked)
  · exact a15ProjectorProfile04BridgeCertificate.bridgeValid
      a15ProjectorProfile04_membership_valid
      (of_decide_eq_true a15ProjectorProfile04_bridgeStatic_checked)
  · exact a15ProjectorProfile05BridgeCertificate.bridgeValid
      a15ProjectorProfile05_membership_valid
      (of_decide_eq_true a15ProjectorProfile05_bridgeStatic_checked)
  · exact a15ProjectorProfile06BridgeCertificate.bridgeValid
      a15ProjectorProfile06_membership_valid
      (of_decide_eq_true a15ProjectorProfile06_bridgeStatic_checked)
  · exact a15ProjectorProfile07BridgeCertificate.bridgeValid
      a15ProjectorProfile07_membership_valid
      (of_decide_eq_true a15ProjectorProfile07_bridgeStatic_checked)
  · exact a15ProjectorProfile08BridgeCertificate.bridgeValid
      a15ProjectorProfile08_membership_valid
      (of_decide_eq_true a15ProjectorProfile08_bridgeStatic_checked)
  · exact a15ProjectorProfile09BridgeCertificate.bridgeValid
      a15ProjectorProfile09_membership_valid
      (of_decide_eq_true a15ProjectorProfile09_bridgeStatic_checked)
  · exact a15ProjectorProfile10BridgeCertificate.bridgeValid
      a15ProjectorProfile10_membership_valid
      (of_decide_eq_true a15ProjectorProfile10_bridgeStatic_checked)
  · exact a15ProjectorProfile11BridgeCertificate.bridgeValid
      a15ProjectorProfile11_membership_valid
      (of_decide_eq_true a15ProjectorProfile11_bridgeStatic_checked)
  · exact a15ProjectorProfile12BridgeCertificate.bridgeValid
      a15ProjectorProfile12_membership_valid
      (of_decide_eq_true a15ProjectorProfile12_bridgeStatic_checked)

theorem a15ProjectorRejection_bridgeCompatible
    (certificate : A15ProjectorProfileCertificate)
    (hcertificate : certificate ∈ a15ProjectorProfileCertificates)
    (rejection : A15ProjectorRejection)
    (hrejection : rejection ∈ certificate.rejections) :
    rejection.witness.bridgeCompatible certificate.profile := by
  have hprofiles :
      ∀ certificate ∈ a15ProjectorProfileCertificates,
        certificate.rejections.all (fun rejection =>
          A15ProjectorWitness.quickCheckBridge certificate.profile
            rejection.witness) = true := by
    simpa only [Array.all_eq_true_iff_forall_mem] using
      a15ProjectorRejections_quickBridge_checked
  have hquick :
      A15ProjectorWitness.quickCheckBridge certificate.profile
        rejection.witness = true := by
    exact (Array.all_eq_true_iff_forall_mem.mp
      (hprofiles certificate hcertificate)) rejection hrejection
  exact rejection.witness.quickBridgeCompatible_sound certificate.profile
    (a15ProjectorProfile_bridgeValid certificate hcertificate) hquick

end SRG266
