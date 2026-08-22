import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0006`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0006Mask : ℕ := 252783263271429

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0006Witness : Array ℤ :=
  #[34, 47, 59, -80, 0, -29, -122, 3, -68, -30, -53, -82, 89, 14, 14, 131,
  109, 43, -46, 44, -72, -24, -73, 70, -43, 128, -27, 48, 120, 35, 37, -21,
  9, -7, -14, 29, -51, 39, 51, 47, -22, -9, 24, -15, 88, -9, 34, -51, -38,
  84, 18, 4, 23, 7, 34, 86, 65, -7, -40, -63, 64, 53, -38, -15, 41, 105,
  -77, -10, 16, 60, 63, 7, -17, 18, -14, 0, 22, 37, 23, 31, 25, 2, 74, 37,
  25, 49, -25, 14, -29, 38, -31, -5, 24, -44, -3, 25, -34, 49, -24, 0, 10,
  41, 19, 29, 34, 1, 4, -16, -23, -1, -14, -60, -101, -52, -52, 92, 59, 20,
  -2, 56, -30, 19, -25, 78, -30, -30, -64, -7, 18, -9, -30, -16, 51, 35,
  -58, 26, -7, 114, -95, -32, -30, -19, -41, 8, -23, 8, 1, 31, -51, -35,
  -51, -88, 61, 65, 34, 24, 54, 20, 25, 17, -83, -9, 70, 50, 48, -23, 32,
  -51]

theorem fractionalNearFrameSubtreeG1R0006_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0006Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0006Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0006Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0006_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0006LowerBoundTable : List ℤ :=
  [1, -24, 138, 64, 10, -71, 115, 183, 103, 10, 273, -131, 132, 157, 257,
  192, 314, 120, 1, 327, -60, -34, 151, 251, 8]

def fractionalNearFrameSubtreeG1R0006LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0006Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0006LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
