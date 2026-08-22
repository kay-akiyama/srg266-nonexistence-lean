import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0166`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0166Mask : ℕ := 1380206701920596

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0166Witness : Array ℤ :=
  #[-81, -117, -2, -26, -23, 42, 100, 150, 85, -107, 14, 17, 104, 28, 113,
  0, 19, -155, 35, -109, -44, 100, 128, 194, 76, -62, 77, 32, 64, 147, 39,
  -76, 203, 13, -1, -9, -87, -67, -4, -151, -7, -30, 14, -128, -67, -76, 0,
  -6, -87, 13, 126, 124, 38, -5, -63, -78, 0, 80, 73, 221, -31, -1, 35, -45,
  -177, -56, 33, 17, 19, 85, -69, -28, 51, 42, 16, 15, -1, -15, -27, -45,
  115, 66, 69, -73, -21, 54, -5, -49, 101, 12, -122, -81, 61, 45, 8, 9, -10,
  43, -24, -125, 22, 4, 127, 55, -144, 76, 26, -2, 43, 89, -64, 131, -129,
  -35, -82, -120, -22, 47, -48, 141, 71, -45, 16, 33, 28, -1, -23, -185, 33,
  -26, 48, -80, -69, 71, 50, 91, 31, 153, -109, 82, -171, 126, 93, 135, 18,
  28, 49, 84, 83, 133, 16, 115, 104, -20, -22, -7, -63, -138, 11, -154, 39,
  -21, -48, -81, 85, 56, 54, -12]

theorem fractionalNearFrameSubtreeG2R0166_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0166Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0166Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0166Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0166_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0166LowerBoundTable : List ℤ :=
  [-30, 156, -9, 177, 40, 2, 197, 104, 2, 46, 317, 252, -92, 80, -47, -235,
  198, 365, 304, 476, 597, 334, 46, 179, -116]

def fractionalNearFrameSubtreeG2R0166LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0166Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0166LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
