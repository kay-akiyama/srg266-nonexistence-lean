/- Copyright (c) 2026. Released under Apache 2.0 license. -/
import SRG266.Certificates.E7SurvivorCheckBase

namespace SRG266

set_option maxRecDepth 100000

theorem e7ResidualCanonicalEligibleCount_fourEightGeneric :
    e7ResidualCanonicalEligibleCount .fourEightGeneric =
      e7ResidualExpectedEligibleCount .fourEightGeneric := by
  decide +kernel

end SRG266
