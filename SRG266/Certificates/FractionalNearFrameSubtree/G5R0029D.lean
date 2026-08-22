import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0029`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0029Mask : ℕ := 1358770118527235

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0029Witness : Array ℤ :=
  #[-264, -193, 748, -372, 1356, -102, -1584, 104, 1598, 0, 1269, -716,
  1362, 0, -582, 484, 291, -1123, -847, 411, 1159, -332, -402, -1236, 0,
  298, 2371, 657, 622, -523, 1633, 2568, 1264, -729, 1238, -1132, 331, 466,
  1480, 647, 344, 1299, -674, 212, 393, 2665, 324, -521, -942, 1704, 674,
  -123, 219, -2125, 546, 315, 166, -569, 1818, 1086, -182, 27, -608, 206,
  1832, 3937, 32, -1289, 2122, -653, -769, 1525, -196, -854, 1955, 486,
  -1244, -1413, 2469, -982, -665, 1990, -128, 90, 2616, -417, 260, 2227,
  879, -708, -409, 326, -260, 1197, 341, -473, 628, 390, 1399, -217, 143,
  96, -187, 1123, 67, -1302, 1344, 945, 1132, -2082, 862, 1069, -3032, 243,
  3101, 889, -2291, -729, 1988, -195, 786, -1076, -2427, 195, 781, -170,
  600, 2333, 1485, 0, 541, -1015, -1047, 1285, -1575, -671, -67, -1079,
  -596, -352, -2006, -523, -315, -448, -84, -175, 734, 160, 1636, 3158,
  -2895, -2256, -1265, -2131, 750, 600, -1190, 1148, -975, 1589, -2294, 354,
  217, -1187, 495, 2103, 525, 1498]

theorem fractionalNearFrameSubtreeG5R0029_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0029Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0029Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0029Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0029_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0029LowerBoundTable : List ℤ :=
  [721, -1486, 2900, 4011, 920, 4372, 1688, 32, 2947, 4706, 2430, -6400,
  -2760, 6376, 2863, 131, 6913, 3196, 2924, 6215, 26, 6382, 9851, 9058, 840]

def fractionalNearFrameSubtreeG5R0029LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0029Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0029LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
