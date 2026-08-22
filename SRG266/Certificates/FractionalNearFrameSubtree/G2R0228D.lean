import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0228`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0228Mask : ℕ := 2496485852418672

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0228Witness : Array ℤ :=
  #[-871, 1649, 1461, -937, 196, -216, 22, 882, 502, 1149, -1261, -615,
  -1006, -978, -848, 221, 334, 589, -560, -806, -1159, -280, -427, -694,
  262, 1227, 952, 935, 652, -449, -825, -651, 620, -774, -975, 1570, 1439,
  1106, 1367, 375, 0, -543, 92, 447, -1307, -1068, -328, -497, 503, 997, 45,
  401, 142, 128, 658, 807, -377, -60, 298, -386, -368, 46, -1385, -2441,
  720, 241, 731, -107, -19, -42, -342, -916, -1870, -272, 579, 600, 510,
  937, 608, -1385, 654, -369, 696, 1536, 580, 723, 338, -332, 955, 296, 413,
  815, 494, 720, -364, 1532, 1576, -12, -1246, -1448, 696, 550, -1052, -165,
  -711, -107, 410, 505, 335, 1203, 87, 776, -11, -254, 681, -1257, -357, 51,
  -103, 0, 955, 687, -118, -614, -246, -783, 59, -166, 37, -466, 557, 319,
  38, 85, -883, -400, -292, -692, -858, 328, -953, -162, 88, -90, 51, 85,
  -119, 2, 350, 138, 135, 1224, 555, 471, 1250, 772, -90, 356, -7, 300, 878,
  1009, -362, -574, 60, -447, 245, 85]

theorem fractionalNearFrameSubtreeG2R0228_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0228Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0228Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0228Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0228_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0228LowerBoundTable : List ℤ :=
  [-88, 214, 33, 1310, -344, -558, 924, 484, 477, 863, 3122, 1247, -169,
  3952, 3146, 100, 584, 5908, 1285, 1233, 4712, 98, 987, -218, 100]

def fractionalNearFrameSubtreeG2R0228LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0228Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0228LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
