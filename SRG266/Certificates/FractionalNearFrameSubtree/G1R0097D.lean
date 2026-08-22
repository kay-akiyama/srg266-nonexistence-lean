import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0097`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0097Mask : ℕ := 946442845397224

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0097Witness : Array ℤ :=
  #[-38, -163, 402, 74, -18, 116, -53, 68, 74, -249, 409, 427, 34, 377, 571,
  16, 266, -50, -246, 302, 293, -5, -273, -289, 247, 180, -90, 3, 164, 0,
  248, 287, 53, 228, -462, 14, 107, 88, 200, -66, -124, -249, -119, -255, 0,
  -160, 69, 183, -43, 50, -86, 22, 107, 370, 46, 269, 348, -316, -147, 189,
  373, 38, -276, -57, -177, 467, 472, 157, -295, 281, 144, 24, 75, -184,
  -90, -20, -353, -11, 256, 191, -246, 131, 130, 253, 321, -39, 385, 194,
  -246, 427, 155, 142, 356, 251, -20, 23, 101, 71, -594, 215, 356, -3, -19,
  320, -194, -98, 91, 173, 466, 236, 454, -133, 266, -77, -235, 115, 132,
  381, -59, 296, -60, 97, 29, -15, -86, -269, -28, -39, -133, 168, 338, 100,
  -147, 22, 128, -82, 66, 176, 244, -362, 389, 183, -251, 229, -119, -395,
  429, 210, 525, 328, 69, 154, -8, -12, -226, -27, 224, 133, -138, -275,
  -283, -302, -181, 287, -118, -74, 44, -22]

theorem fractionalNearFrameSubtreeG1R0097_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0097Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0097Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0097Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0097_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0097LowerBoundTable : List ℤ :=
  [496, 330, 387, 281, 597, 1316, 531, 371, 738, 1590, 371, -25, 674, 855,
  638, 499, 1172, 1016, 351, -18, 2170, 1431, 733, 1109, 1945]

def fractionalNearFrameSubtreeG1R0097LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0097Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0097LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
