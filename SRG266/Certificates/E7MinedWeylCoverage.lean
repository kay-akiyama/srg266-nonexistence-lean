/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Certificates.E7MinedWeylData

/-! # Source and target coverage of the mined E7 Weyl certificates -/

namespace SRG266

theorem e7MinedWeylSources_cover :
    e7MinedWeylSourceProfiles.toFinset =
      e7MinedComponentProfiles.toFinset := by
  decide +kernel

theorem e7MinedWeylTargets_cover :
    e7MinedWeylTargetProfiles.toFinset =
      e7MinedWeylCanonicalProfiles.toFinset := by
  decide +kernel

end SRG266
