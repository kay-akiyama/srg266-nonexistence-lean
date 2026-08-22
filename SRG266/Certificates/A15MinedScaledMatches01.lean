/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Certificates.A15ProjectorData.Profile08
import SRG266.Hosts.A15MinedNormProfileData
import SRG266.Hosts.A15MinedSearch

/-! # Bounded scaled-profile matches for the mined A15 transport -/

namespace SRG266

theorem a15MinedNormProfile06_projector08 :
    a15SmallProfile a15MinedNormProfile06 =
      a15ProjectorProfile08.profile.centroidVector := by
  decide +kernel

end SRG266
