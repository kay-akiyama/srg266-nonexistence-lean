/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Certificates.A15ProjectorAudit.Profile00
import SRG266.Certificates.A15ProjectorAudit.Profile01
import SRG266.Certificates.A15ProjectorAudit.Profile08
import SRG266.Certificates.A15ProjectorAudit.Profile12

/-!
# Minimal bridge facts for the four final A15 profiles

The final transport consumes only projector profiles 0, 1, 8, and 12.  Keep
their audited orbit bridges separate from the thirteen-profile aggregate so
the mined proof path does not load the nine rejected projector profiles.
-/

namespace SRG266

theorem a15ProjectorProfile00_bridgeValid :
    a15ProjectorProfile00.profile.bridgeValid :=
  a15ProjectorProfile00BridgeCertificate.bridgeValid
    a15ProjectorProfile00_membership_valid
    (of_decide_eq_true a15ProjectorProfile00_bridgeStatic_checked)

theorem a15ProjectorProfile01_bridgeValid :
    a15ProjectorProfile01.profile.bridgeValid :=
  a15ProjectorProfile01BridgeCertificate.bridgeValid
    a15ProjectorProfile01_membership_valid
    (of_decide_eq_true a15ProjectorProfile01_bridgeStatic_checked)

theorem a15ProjectorProfile08_bridgeValid :
    a15ProjectorProfile08.profile.bridgeValid :=
  a15ProjectorProfile08BridgeCertificate.bridgeValid
    a15ProjectorProfile08_membership_valid
    (of_decide_eq_true a15ProjectorProfile08_bridgeStatic_checked)

theorem a15ProjectorProfile12_bridgeValid :
    a15ProjectorProfile12.profile.bridgeValid :=
  a15ProjectorProfile12BridgeCertificate.bridgeValid
    a15ProjectorProfile12_membership_valid
    (of_decide_eq_true a15ProjectorProfile12_bridgeStatic_checked)

end SRG266
