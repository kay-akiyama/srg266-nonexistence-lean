import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0100`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0100Mask : ℕ := 1247519827288353

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0100Witness : Array ℤ :=
  #[-83, -137, -66, -129, -206, -97, 81, 71, 38, 122, 89, 63, -27, 25, -21,
  0, 197, 40, 100, 30, -54, -45, -59, -17, 24, 18, -35, 31, -9, -53, 80,
  -45, 116, 21, 63, 13, -30, -19, 0, -12, -116, -81, -12, -81, 43, -120,
  -72, 40, -16, 131, 34, -128, -40, 26, 16, -112, -134, -110, 17, 17, 6,
  -103, -160, 133, 8, 1, 11, 41, 7, 44, 87, 51, 1, -8, -8, -43, -65, -24,
  33, 82, -57, 108, -44, 47, 56, -65, -129, 47, 5, 47, 31, -24, -1, 46, 17,
  12, 45, 56, -2, -60, 40, 37, 25, 3, 100, 72, 40, -117, -85, -138, -62,
  -65, -124, 24, -68, 30, 10, 89, 96, 5, -59, 15, 26, -87, -30, -16, 61, 34,
  10, -136, -102, 18, 10, -93, 13, 48, -25, -41, 12, 14, 47, 31, -131, -130,
  8, -1, -53, 10, 26, -14, 18, -6, 19, 0, 3, 20, -44, 34, -35, 96, 14, 27,
  141, 42, 12, -117, -30, 17]

theorem fractionalNearFrameSubtreeG2R0100_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0100Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0100Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0100Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0100_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0100LowerBoundTable : List ℤ :=
  [-161, -62, -82, -69, 4, 29, -90, -97, -86, -150, 210, -219, -216, 240,
  -134, -130, -219, 137, -140, 151, 96, -160, 162, 10, 11]

def fractionalNearFrameSubtreeG2R0100LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0100Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0100LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
