/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Certificates.E7ScalarDPData

/-!
# Assembly API for the audited E7 scalar DP

This module projects the scalar-DP audit interface into the single inclusion
consumed by the concrete-enumeration assembly.
-/

namespace SRG266

variable [E7ScalarDPAuditInput]

theorem trace_pair_mem_listed_keys
    (pair : E7ComponentKey × E7ComponentKey)
    (hpair : pair ∈ e7TraceFeasibleHistogramPairs) :
    pair ∈ e7ListedCentroidHistogramPairsUpToSwap :=
  E7ScalarDPAuditInput.trace_subset pair hpair

end SRG266
