/- Copyright (c) 2026. Released under Apache 2.0 license. -/
import SRG266.Certificates.E7SurvivorCheckBase

namespace SRG266

set_option maxRecDepth 100000

theorem e7ResidualCanonicalEligibleCount_sixGenericSixSpecial :
    e7ResidualCanonicalEligibleCount .sixGenericSixSpecial =
      e7ResidualExpectedEligibleCount .sixGenericSixSpecial := by
  decide +kernel

end SRG266
