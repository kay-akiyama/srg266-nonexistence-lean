import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0566`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0566Mask : ℕ := 6846371567486474

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0566Witness : Array ℤ :=
  #[1557, -1059, 1039, 151, -2307, -1207, 1037, -287, 1318, -1615, -295,
  2309, 1154, 1356, 924, -674, 1219, 907, 1367, -880, -754, -636, -742, 902,
  57, -908, 913, 465, 392, -405, -37, 2397, -1681, 2084, -1909, -980, 2327,
  -1092, 335, -127, -3410, -2166, -162, -490, -255, 619, -1702, 48, 611,
  767, -9, -1121, -126, 370, 2104, -366, -923, 305, 12, 22, -1046, -163,
  1782, -1005, -1447, 555, -1387, -1228, -1477, 1454, 416, -882, -272, -807,
  -759, 2439, -246, -1142, -606, 447, -328, 0, -1387, -742, -1690, 15, 279,
  71, 1068, 493, 1210, 2287, 2195, 3302, -311, -240, 614, 1236, -1953, 1112,
  184, -202, -10, 680, 729, -1248, -2148, 3048, 1053, 1227, -1138, -1469,
  -4, -849, -999, -1474, 841, -2019, -885, 251, 1682, 2710, 508, -618, 340,
  1448, 1332, 526, 1234, 1629, 111, 1342, -494, -568, -862, -290, -137,
  1426, -1265, 29, 1614, 0, -943, 2006, -75, 2585, 239, 2139, 1129, -248,
  932, 974, -1545, 172, -1972, -174, 980, 64, -461, 272, 1677, -1349, -952,
  -118, -251, 2445, 643, 327]

theorem fractionalNearFrameSubtreeG2R0566_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0566Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0566Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0566Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0566_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0566LowerBoundTable : List ℤ :=
  [-1086, 2242, -1395, 2909, 32, -518, -322, 2272, 2777, 5152, 702, 9543,
  3888, 7406, 827, -612, -801, 79, 2433, 7477, -642, -2607, 577, 407, 3077]

def fractionalNearFrameSubtreeG2R0566LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0566Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0566LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
