import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0446`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0446Mask : ℕ := 5791992797076632

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0446Witness : Array ℤ :=
  #[-97, 36, -109, -211, -18, 203, 364, 301, 345, 72, 182, -66, -9, -187,
  111, 384, -547, 124, -573, 334, 419, 42, -85, 135, 32, -375, 18, -132,
  323, 123, 216, -289, -128, 109, 225, 144, 177, -467, 126, 52, -6, 247,
  139, 429, 479, -37, -139, -256, 350, 8, 535, -565, -227, -420, 489, 411,
  385, -60, -20, 252, 305, -128, 320, 399, 98, -244, -283, 243, 195, 318,
  -267, -291, 498, 147, -58, -94, -106, 174, 61, 106, 745, 214, 23, 743,
  -197, 407, -7, -182, 105, 73, -27, -83, 193, 92, -94, 175, -153, 13, 145,
  -63, 94, 156, 342, 247, 487, -465, 9, 51, 225, -191, -160, -252, -319,
  224, 418, 193, 2, -30, 265, 84, 26, -50, -44, -180, 295, 385, -105, -493,
  -219, 143, 46, -9, -103, -275, 667, 106, -77, -293, 195, -303, 615, 464,
  -160, -203, 212, -387, 98, -196, 175, 111, 89, 373, 208, -170, 187, 322,
  0, 43, -38, 463, 249, 192, -523, 437, 45, 228, 150, 419]

theorem fractionalNearFrameSubtreeG2R0446_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0446Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0446Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0446Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0446_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0446LowerBoundTable : List ℤ :=
  [548, 763, 809, 300, 620, 409, 833, 1235, 455, 987, 728, 2451, -646, 1598,
  2066, 2452, 972, -65, 10, 1606, 8, 506, 11, 1498, 2046]

def fractionalNearFrameSubtreeG2R0446LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0446Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0446LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
