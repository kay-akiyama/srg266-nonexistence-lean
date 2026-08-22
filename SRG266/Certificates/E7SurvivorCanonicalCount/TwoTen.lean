/- Copyright (c) 2026. Released under Apache 2.0 license. -/
import SRG266.Certificates.E7SurvivorCheckBase

namespace SRG266

set_option maxRecDepth 100000

theorem e7ResidualCanonicalEligibleCount_twoTen :
    e7ResidualCanonicalEligibleCount .twoTen =
      e7ResidualExpectedEligibleCount .twoTen := by
  decide +kernel

end SRG266
