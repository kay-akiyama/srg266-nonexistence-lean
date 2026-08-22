/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Certificates.A15MinedExceptionalData
import SRG266.Certificates.A15ProjectorData.Profile12
import SRG266.Hosts.A15MinedNormProfileData
import SRG266.Hosts.A15MinedSearch

/-! # Bounded scaled-profile matches for the mined A15 transport -/

namespace SRG266

theorem a15MinedNormProfile02_projector12 :
    a15SmallProfile a15MinedNormProfile02 =
      a15ProjectorProfile12.profile.centroidVector := by
  decide +kernel

theorem a15MinedNormProfile15_exceptional00 :
    a15SmallProfile a15MinedNormProfile15 =
      (a15MinedExceptionalCertificates.get ⟨0, by decide⟩).toCertificate.d := by
  decide +kernel

theorem a15MinedNormProfile00_exceptional01 :
    a15SmallProfile a15MinedNormProfile00 =
      (a15MinedExceptionalCertificates.get ⟨1, by decide⟩).toCertificate.d := by
  decide +kernel

end SRG266
