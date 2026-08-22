import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G4R0012`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0012Mask : ℕ := 4869653626994819

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0012Witness : Array ℤ :=
  #[506, -37, -268, 1389, -15, 1155, -629, -54, -440, 899, -280, -1128,
  -977, 0, 594, 0, 819, -292, 216, 1351, 257, 1520, -859, -17, 188, 1441,
  105, 142, 0, -196, -553, -320, 2017, 2270, 1428, 2277, 233, -497, -2028,
  -1933, -1833, -1583, -999, -1457, 256, 432, -583, -1792, -352, 408, 1410,
  -163, 400, -1338, 1344, 102, 1591, 865, -429, -827, -43, 662, 1222, 1801,
  324, -116, -653, 563, 26, -223, -83, 568, -786, 95, 43, 818, 431, 57,
  -963, -680, -294, -1475, 835, 47, 237, -1081, 383, 1829, 503, 1112, -180,
  -814, -914, 774, -934, 59, 563, -481, -2407, 1079, 133, -629, 873, -188,
  152, -221, -398, -169, -1492, 803, 456, 1851, -491, -44, 620, 202, -339,
  -1152, -924, -1116, 835, 2852, -85, 342, 104, -198, -629, -10, 1300, 761,
  207, 853, -308, -338, 115, 2430, -1098, -1436, 734, 850, -301, 255, -715,
  -2619, -416, -64, -1498, -388, 52, 1359, -722, 200, -41, -447, -228, 742,
  265, 622, 575, 745, 582, 678, -461, -161, 1459, 128, -337, -79]

theorem fractionalNearFrameSubtreeG4R0012_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0012Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0012Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0012Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0012_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0012LowerBoundTable : List ℤ :=
  [-177, 73, 2118, 919, -1531, 1934, 33, 522, -1251, 4482, -2032, 836, 554,
  101, 100, 3046, 836, 7876, 1838, 863, 101, 100, 3950, -312, 2397]

def fractionalNearFrameSubtreeG4R0012LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0012Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0012LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
