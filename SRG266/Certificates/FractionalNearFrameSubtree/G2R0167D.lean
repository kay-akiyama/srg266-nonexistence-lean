import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0167`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0167Mask : ℕ := 1380209897882708

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0167Witness : Array ℤ :=
  #[-2483, -1240, -2221, 0, -2963, -2524, 2157, 1335, -756, -913, 1114,
  1823, 3573, 617, 1763, 3103, 939, -72, -200, 1001, -1930, -268, 2513,
  1361, 656, -1975, -1139, -132, -1176, -860, 1083, 192, 378, 590, -462,
  -1023, 931, -678, -1364, 497, -631, -1076, -116, 797, -1215, -1349, 224,
  445, 442, 997, 1851, 177, 846, -229, -186, 84, -1263, -940, -607, 2701,
  -331, 2370, 646, -359, 628, 1256, -1062, 61, -1963, 351, 1106, 928, 111,
  1111, -568, 1116, -856, -413, 1270, 1267, 1258, -1745, -279, 550, -307,
  -511, 825, -1644, -1064, 2228, 1193, -546, 1945, 2, -1561, -830, 766, 619,
  3066, 78, -304, 2064, 489, 1826, 2040, -2168, -715, 312, -566, -1068, 14,
  -1002, 397, 1101, 2357, 1162, 454, 2143, 299, 1046, 700, 52, -1254, -2338,
  -985, 1267, -1294, 819, 1244, 304, -606, -1078, 465, -12, 1043, -662,
  -1169, -778, 1526, 730, -790, 2145, -314, 1531, 269, -170, 1059, -717,
  562, 257, -723, -1504, -476, -601, 255, 1050, -505, 881, 452, -1420, 1280,
  -402, 919, -318, 480, -801, 144, 435]

theorem fractionalNearFrameSubtreeG2R0167_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0167Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0167Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0167Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0167_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0167LowerBoundTable : List ℤ :=
  [409, 1353, 1502, 1206, 1726, 812, 32, 1569, 31, 441, -2697, 2207, -284,
  4183, 99, 3796, 100, 5480, -846, 3623, 10718, 1391, 13890, 2577, 3192]

def fractionalNearFrameSubtreeG2R0167LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0167Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0167LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
