/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Certificates.A15ProjectorData.Profile00
import SRG266.Certificates.A15ProjectorData.Profile01
import SRG266.Hosts.A15MinedNormProfileData
import SRG266.Hosts.A15MinedSearch

/-! # Bounded scaled-profile matches for the mined A15 transport -/

namespace SRG266

theorem a15MinedNormProfile16_projector00 :
    a15SmallProfile a15MinedNormProfile16 =
      a15ProjectorProfile00.profile.centroidVector := by
  decide +kernel

theorem a15MinedNormProfile14_projector01 :
    a15SmallProfile a15MinedNormProfile14 =
      a15ProjectorProfile01.profile.centroidVector := by
  decide +kernel

end SRG266
