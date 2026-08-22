import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0083`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0083Mask : ℕ := 1041801917599984

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0083Witness : Array ℤ :=
  #[55, -16, 102, 77, 28, -108, 44, 46, -20, 0, -96, -150, 90, 47, 33, -22,
  19, 61, 28, -58, -108, 34, 65, -71, -134, 1, -3, 86, 32, 91, 12, 77, -55,
  -49, -50, -72, -67, -70, -40, -62, -31, 82, -9, -26, -34, 89, 7, -38, 58,
  47, -3, 5, 8, -74, 57, 16, -116, -37, 40, 139, 46, -41, 28, -70, -113, 33,
  -1, 48, 143, -6, 54, -95, -90, -120, 5, -47, 97, 46, -28, -26, -114, 84,
  4, 19, -43, 51, -31, 155, 5, 65, 17, -86, -108, -18, -8, -125, 2, -91,
  -56, -29, 50, 75, 114, -93, 27, -164, 100, 144, 96, 127, -76, 2, 14, -22,
  1, -87, -47, 30, 84, -36, 153, 136, 98, -17, -23, -8, -50, -23, 11, -33,
  -13, 14, 41, 65, 52, 130, -18, 37, -45, -57, -47, 43, 85, -44, -88, 108,
  180, -54, 90, -76, 0, 57, 16, 98, 27, 33, -92, -83, -118, 8, 113, 61, -65,
  -55, 59, 177, 84, 25]

theorem fractionalNearFrameSubtreeG2R0083_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0083Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0083Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0083Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0083_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0083LowerBoundTable : List ℤ :=
  [-61, 225, 1, 152, 40, 2, 77, 0, 7, 149, 438, 120, -42, -49, 210, -212,
  -29, 115, 204, 79, 272, -285, 475, -37, 10]

def fractionalNearFrameSubtreeG2R0083LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0083Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0083LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
