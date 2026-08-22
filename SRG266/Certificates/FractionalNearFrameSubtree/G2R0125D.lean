import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0125`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0125Mask : ℕ := 1345575297320006

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0125Witness : Array ℤ :=
  #[-413, 420, -94, -1406, -1560, -1239, -590, 0, 377, -178, 282, 386, 306,
  1340, 965, 1830, 829, 84, -611, -1748, -1137, -89, 779, -64, -323, -384,
  -86, 957, 1110, 927, 1590, 0, 1996, 1618, -649, -327, -491, -420, -603,
  -453, -343, -677, -744, 1259, -1272, -355, 350, 219, -94, -582, -1931,
  -1367, 284, 1339, 339, -137, -863, -1098, 693, -753, 943, 527, -442, 815,
  -344, 292, -1817, -632, -721, 298, -186, 469, -86, -965, 705, 788, 223,
  842, 294, -237, -316, -463, 656, 942, -179, 958, 432, 381, 664, -149,
  -222, 842, 669, 1109, 278, -48, -431, -35, 560, -122, -203, -295, 832,
  355, 309, 1433, 425, -373, 0, -316, 1267, -244, 460, -685, 608, -1235,
  231, 398, 452, -1060, -236, -1062, 1113, 48, 596, -477, -389, 153, 591,
  -358, 693, -587, 571, 1333, 75, 248, 541, 780, 959, -441, -1272, -1221,
  792, -58, -398, 441, 603, -1343, 842, -802, -419, 642, 423, 586, 334,
  -322, 1389, -552, -730, -883, -571, -1143, -1633, 569, 664, -689, -1210,
  1634]

theorem fractionalNearFrameSubtreeG2R0125_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0125Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0125Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0125Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0125_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0125LowerBoundTable : List ℤ :=
  [-889, -1011, -896, 1637, 31, -850, 870, 32, 1532, 165, 1522, 326, 3572,
  2492, 4133, 2359, -908, 1213, 466, 863, 2138, 101, 3595, -1166, -2667]

def fractionalNearFrameSubtreeG2R0125LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0125Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0125LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
