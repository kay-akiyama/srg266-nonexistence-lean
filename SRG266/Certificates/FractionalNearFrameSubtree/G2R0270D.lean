import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0270`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0270Mask : ℕ := 5369794277842456

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0270Witness : Array ℤ :=
  #[46, 104, 74, 49, 81, -44, -84, 55, -16, -119, -67, -44, 6, -40, 19, -58,
  -21, -32, -12, 112, 85, -1, 101, 0, 33, 25, 12, 19, -43, -30, -51, -27,
  -10, 170, -38, 56, 48, -6, 47, 36, 51, 12, 3, 16, -104, 94, 1, -71, -71,
  -13, 51, 6, -14, 0, -66, -235, 44, -65, 6, -58, -12, 188, -42, 98, 151,
  62, -61, 81, 3, 37, -26, 35, -107, -33, 164, -76, -44, -187, 44, 9, 150,
  -60, 64, 13, -31, -249, 42, -18, 56, 111, -52, 30, -93, 10, 32, 11, -1,
  -96, 58, -103, 74, -171, 3, 125, 182, 129, 5, 120, -132, -3, -2, 71, 66,
  -8, 41, 4, 137, 214, 180, 242, -231, -123, 9, -94, -13, 21, -38, -24, 44,
  -57, 118, -92, -117, -46, 36, -16, 57, -77, -90, -142, -46, 21, -55, -31,
  119, -125, 99, 19, 106, -45, -58, -33, 59, 2, -26, 101, 76, 34, -40, -123,
  80, -127, 6, -3, -132, -137, 0, -105]

theorem fractionalNearFrameSubtreeG2R0270_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0270Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0270Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0270Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0270_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0270LowerBoundTable : List ℤ :=
  [-45, -77, -40, 113, 86, -104, 75, -90, 52, 154, 268, -134, -120, 10,
  -152, 221, -23, 234, 10, 247, 10, 151, 51, 126, -97]

def fractionalNearFrameSubtreeG2R0270LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0270Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0270LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
