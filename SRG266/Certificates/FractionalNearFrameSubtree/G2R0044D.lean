import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0044`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0044Mask : ℕ := 901173664535073

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0044Witness : Array ℤ :=
  #[-191, -206, -187, -200, -81, -78, 167, 141, 106, 107, 128, 117, 29, 70,
  6, 0, -1, -4, 9, 35, 12, 12, 67, -74, 18, 0, -21, -32, 32, 22, 22, 40, 25,
  48, -6, 43, -53, -37, -29, -58, 63, 66, 42, 2, -65, -2, 31, 212, 83, -63,
  -39, -11, -14, -89, -53, -12, -30, -16, 41, 178, -78, -35, 34, 51, 30, 23,
  27, -45, 52, -56, 66, -52, -54, 97, -25, 69, 40, -28, 30, -39, -12, 48,
  12, 48, 121, -41, -92, -81, -116, 99, 74, 80, 54, 52, 23, 98, 114, 31, 48,
  45, 57, -127, -114, -90, -82, -53, -86, -83, -95, -95, -105, -117, -101,
  110, 152, 47, 41, -109, -125, -34, 0, -179, -22, -7, -100, -112, -11, 27,
  -143, -11, 12, -15, 20, -29, 80, 0, -22, -14, 13, -45, 107, -7, 4, -9, -4,
  79, 7, -12, 15, 4, 102, 5, 4, -135, 51, 52, -105, 15, 92, -35, 2, 128,
  -45, 100, 4, 124, -13, -195]

theorem fractionalNearFrameSubtreeG2R0044_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0044Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0044Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0044Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0044_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0044LowerBoundTable : List ℤ :=
  [-72, 2, 0, 2, 1, 63, -42, -14, -105, -68, -94, -39, -149, 9, 290, 167,
  -211, -8, 293, -240, 164, 10, 92, 11, -115]

def fractionalNearFrameSubtreeG2R0044LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0044Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0044LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
