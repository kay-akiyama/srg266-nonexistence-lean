import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0024`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0024Mask : ℕ := 468078187688453

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0024Witness : Array ℤ :=
  #[-7, 129, 24, -5, 0, 228, 242, 156, 59, 70, 191, 126, -224, -117, -88,
  -246, -212, -213, -55, -41, -74, -223, 43, -35, -49, 58, -85, -68, 194,
  49, 191, 244, -37, -32, -98, -63, 120, 59, -28, -5, 31, 154, 57, -9, 44,
  -123, 65, 49, 34, 140, 140, 0, -58, -46, 59, 171, 76, -85, 18, -21, -45,
  51, -73, -32, 39, 173, 183, -2, -2, 60, 76, 152, 34, -11, 66, -101, 57,
  30, -60, 81, -45, 38, 49, 2, 182, 77, 21, 50, 5, 45, -66, 32, 58, 21, 21,
  145, 69, 62, -41, 33, -11, -16, -29, -95, -96, -20, -17, -134, -93, -89,
  -95, -165, -4, 35, -11, 10, -3, 57, 8, 20, 10, 97, 16, 41, 30, -60, 25,
  -46, -23, 18, -38, -34, 94, 1, -23, 67, 11, 103, -29, 223, 83, 69, 46, 62,
  11, 77, -15, -34, -30, -56, 74, -13, 152, 99, 7, 3, 54, 109, 1, -11, -69,
  111, -15, -12, 21, 19, -12, 10]

theorem fractionalNearFrameSubtreeG1R0024_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0024Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0024Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0024Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0024_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0024LowerBoundTable : List ℤ :=
  [115, 161, 142, 48, 73, 320, 352, -38, 328, 279, 162, 50, 500, 314, 254,
  266, 374, 53, 136, 170, 292, 293, 76, 226, 623]

def fractionalNearFrameSubtreeG1R0024LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0024Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0024LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
