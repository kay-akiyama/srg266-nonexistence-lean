import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0284`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0284Mask : ℕ := 5373076711185072

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0284Witness : Array ℤ :=
  #[-290, 94, 56, -204, 220, 102, -22, 214, 179, 86, 7, 7, 498, 277, 146,
  -23, 24, 266, -25, 455, -298, 108, 30, 73, -148, -489, 0, 311, 215, 455,
  110, 136, -124, -31, -178, 78, 233, -275, 257, 68, -43, 242, 16, 366,
  -208, 362, 75, -181, 46, 118, -185, 240, 98, 316, 0, -395, -211, 88, 225,
  304, -147, 5, 112, 604, -533, 207, 262, 40, -375, 297, -428, 312, 171,
  -601, -120, -350, 100, 56, 2, 17, 172, 107, -86, 14, 259, 20, -100, -303,
  -224, -220, -112, -388, 106, 14, -256, 101, -69, -195, -62, -62, -380,
  466, 21, 128, -51, 200, 274, 243, 16, 269, -360, -197, -525, -530, -271,
  -259, 124, -9, 191, 351, 468, 398, 6, -151, 89, -127, -80, -358, 12, -119,
  14, 98, -288, 185, -128, -109, 158, 58, -7, 67, 44, -21, -16, 111, 264,
  52, 84, 98, -126, 516, 167, 211, -93, 158, -360, -130, -119, -80, -527,
  -260, 67, 187, -8, 392, -11, 50, -958, -220]

theorem fractionalNearFrameSubtreeG2R0284_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0284Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0284Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0284Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0284_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0284LowerBoundTable : List ℤ :=
  [-150, -282, -193, 2, 2, 3, 446, -111, 358, 366, 783, -18, 356, 245, 4,
  200, 1223, -505, 823, 293, 609, -654, 822, 158, 10]

def fractionalNearFrameSubtreeG2R0284LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0284Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0284LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
