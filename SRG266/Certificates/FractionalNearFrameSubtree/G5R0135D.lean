import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0135`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0135Mask : ℕ := 6074150378373346

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0135Witness : Array ℤ :=
  #[166, 2026, -349, -319, 1044, -284, 1350, 0, 835, 1359, 184, -809, -392,
  -906, 1441, 2707, -540, 427, 278, -270, 943, 1824, -1759, -206, -1132,
  852, 451, 1771, 467, 734, 1239, 683, -984, -1395, -568, -1559, -39, -526,
  2325, 2567, 1066, -1243, 1585, 4002, 3219, 882, -1385, 1653, -1715, 641,
  -1148, 1823, -523, 613, 815, 831, 1530, -569, 1499, 431, -1487, -274, 405,
  -103, -1104, 1289, 274, -480, -322, 127, 606, -125, -205, 1123, 3955, 394,
  1091, 212, 1998, 1377, -1247, 1875, -558, 1782, -138, 2786, -1736, 2313,
  860, 1457, 674, -693, 0, 467, -590, -673, 1407, 125, 8, 2537, 1835, -376,
  1105, -1007, 670, -574, 2153, 1254, 273, -1832, 914, 83, 1556, -1089,
  3815, -708, 512, 809, 2095, -1936, 593, 392, 1080, 618, 199, -586, -371,
  1848, 1216, -711, 1350, 2050, -1011, 998, 395, 2391, 429, -1143, -882, 0,
  25, 430, 735, 0, 947, 224, 933, 433, -1158, -1098, -987, 354, 213, -712,
  2191, 869, -321, 513, 89, 1285, 1082, -1522, -146, -1265, 9, 737, -939,
  -1655]

theorem fractionalNearFrameSubtreeG5R0135_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0135Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0135Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0135Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0135_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0135LowerBoundTable : List ℤ :=
  [3764, 1655, 5928, 3259, 1656, 5868, 5828, 3926, 6483, 7535, 2370, -613,
  14085, 3023, 9632, 4904, 9757, 101, 2056, 5289, 6117, 1801, 2229, 9176,
  10164]

def fractionalNearFrameSubtreeG5R0135LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0135Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0135LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
