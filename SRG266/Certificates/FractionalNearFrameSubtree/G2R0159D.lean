import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0159`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0159Mask : ℕ := 1379519618318946

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0159Witness : Array ℤ :=
  #[-47, 108, 6, 114, 0, 158, -310, -216, -163, -87, -29, 36, 35, -20, 27,
  145, 109, -40, -48, 8, -112, -97, -77, -188, 33, 153, -2, 74, 35, 12, 8,
  65, 37, -12, -32, 0, 16, -98, 141, -66, -47, 14, -148, -43, -50, -64,
  -103, -100, 141, 186, 50, 104, 22, 70, 38, -66, -298, 12, -32, -80, -138,
  5, 76, 225, 9, -93, 84, 65, 46, 89, -61, -125, -30, -64, -153, 146, -2,
  87, 5, -113, -6, -24, 3, 193, 16, 11, 100, 47, 19, 27, 114, 48, 130, -108,
  -18, -10, -24, 25, -79, 119, 17, 14, 139, 65, 112, -267, -122, 76, -35,
  -42, 23, 58, -33, 266, -138, -160, -4, 56, 41, 76, 173, 44, -12, -155, 65,
  157, 26, 72, 18, 240, -73, -46, 50, 52, 15, -1, 157, -22, -64, 7, 16, 118,
  -45, -65, 103, 29, 53, -235, -179, 61, -23, 104, -207, 40, 38, 1, 81, 72,
  -40, -40, 109, 37, -70, 156, 126, -197, 55, -35]

theorem fractionalNearFrameSubtreeG2R0159_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0159Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0159Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0159Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0159_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0159LowerBoundTable : List ℤ :=
  [-137, 43, -138, 29, 221, 176, 14, -38, -229, 453, 189, -101, 9, 447, 11,
  12, 121, 116, 774, 182, 10, 9, 515, 109, 11]

def fractionalNearFrameSubtreeG2R0159LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0159Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0159LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
