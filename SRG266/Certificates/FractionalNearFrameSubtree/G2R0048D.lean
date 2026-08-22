import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0048`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0048Mask : ℕ := 931890231624268

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0048Witness : Array ℤ :=
  #[754, 684, -280, -1389, -1576, 801, 211, 1106, 1805, 1466, -781, 482,
  -305, -443, 667, 807, 2215, 620, 1415, -90, 258, -394, -228, 270, -824,
  -1063, 1598, -858, 2068, -443, 366, 842, 1738, -704, -222, 1470, 74, -278,
  -1419, -885, -606, 164, -1002, 0, 1549, -7, 167, 101, 188, -1361, -539,
  -420, -452, 1225, 49, 1046, -1224, -142, 154, 698, 490, 654, 437, 1682,
  693, 375, -437, -635, 2456, 92, 907, 811, 304, 325, 265, 586, 1182, -977,
  316, 632, 489, -118, 390, 570, 87, 823, -441, 2146, 1921, -83, 1185, 1008,
  -585, -1182, -161, 1021, -163, 915, -462, 783, 1297, 692, 1466, 1158,
  1818, -288, 1751, -1582, 1201, -212, -340, 0, 1243, 830, -414, 610, 1590,
  -920, 514, -1188, 699, -1128, 670, 326, -1439, 584, -624, 327, 2053, 641,
  -1068, -1293, 1285, 817, 1954, -897, -182, 12, 493, 640, 2226, -422,
  -1067, -143, -105, -200, -153, -8, 1364, 275, 954, 559, 658, 1346, -484,
  423, 1609, 29, 976, 20, -1321, 496, 2712, 1551, 996, -1044, -397, 0]

theorem fractionalNearFrameSubtreeG2R0048_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0048Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0048Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0048Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0048_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0048LowerBoundTable : List ℤ :=
  [2094, 3324, 4142, 4917, 2283, 4755, 1709, 3719, 3852, 5074, 2519, 3010,
  1359, 7449, 4660, 1280, 2787, 6597, 5392, 6602, 5062, 100, 1503, 4431,
  6447]

def fractionalNearFrameSubtreeG2R0048LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0048Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0048LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
