import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0039`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0039Mask : ℕ := 538369639456972

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0039Witness : Array ℤ :=
  #[1378, -590, -13, -772, -748, 938, 629, 430, 311, 413, -867, -254, -459,
  -564, 241, -1205, -802, -698, -1112, 550, 456, 170, -204, 222, 702, 1947,
  224, 6, 1448, 282, -13, -343, -97, -714, -678, -182, 223, 0, 586, -461,
  -910, -617, -1218, -2120, -1672, -1978, 902, 1073, 847, 1089, -109, 1588,
  -666, 1055, 1089, 1221, 1871, 17, -110, -829, 773, -744, 1116, 1124, -401,
  -330, 236, 681, 35, 769, -212, -652, -465, 20, 430, -885, 339, -40, 72,
  -682, 1288, 246, -555, 540, 320, 135, -372, 147, 171, 1318, 67, -424, 177,
  474, 1026, 130, 338, -192, 537, -220, 1040, 176, 477, -91, 441, 776, -175,
  1097, 1230, -44, 557, 444, -573, 185, 772, -10, -1152, 183, 620, -1439,
  366, -558, 1277, -66, 985, 690, -1194, 932, 78, -139, -1455, -480, -259,
  626, -446, 75, -202, -118, 754, 169, -310, 726, -171, -281, -416, 685,
  590, -268, -813, 94, 981, 283, -967, -1088, 323, -84, -13, 352, 110, -45,
  -339, 610, -696, -185, -113, 81, 120, 151]

theorem fractionalNearFrameSubtreeG1R0039_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0039Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0039Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0039Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0039_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0039LowerBoundTable : List ℤ :=
  [45, -418, 1384, 11, 1207, 719, 1936, 514, 1114, 4184, 2323, -93, 641,
  3060, 3483, 1698, -1279, 245, 942, -990, 1285, 1608, 1608, 763, -139]

def fractionalNearFrameSubtreeG1R0039LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0039Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0039LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
