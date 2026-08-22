import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0139`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0139Mask : ℕ := 1358770369664138

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0139Witness : Array ℤ :=
  #[486, 1135, 261, -1943, -522, -356, 563, 223, 0, 1645, 1243, 943, -534,
  -407, 86, 446, 1221, 1126, 446, -128, -434, 604, -1010, 196, 658, -9, 380,
  983, 219, 44, 1666, 651, 172, -131, -240, 68, -1221, 1529, -610, -962,
  462, -1191, 960, 591, 0, 1626, 152, 580, -449, 937, 1779, -311, -808,
  -996, 1560, 980, -341, -1973, -404, 863, -540, -1511, -792, 438, 433,
  1299, 1408, -1086, -1706, 305, -132, 406, -1420, 1442, 837, -1304, 317,
  -1038, 617, 766, 1330, 1489, 1635, -361, 319, 239, 1596, -330, -2327, 816,
  -97, -129, 234, 853, 295, 1985, -146, -920, 1047, 833, 189, 1055, -454,
  1463, -245, 310, 2186, 902, 1532, 628, 592, 1174, -2538, -988, 0, 965,
  -2150, 759, 488, -669, -837, 1650, 59, 507, 1747, 1644, 56, 875, -347,
  -178, 835, -2161, 905, 989, 1489, 55, -407, 1591, 1266, -1466, -278,
  -1454, -322, -726, -211, -1542, -559, -422, 139, 1518, -383, 815, -212,
  -287, 206, 364, -1313, 829, 457, 899, 157, 2228, -2319, 940, -1568, 1024,
  -322, 1606]

theorem fractionalNearFrameSubtreeG2R0139_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0139Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0139Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0139Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0139_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0139LowerBoundTable : List ℤ :=
  [1402, 1644, 2739, 1522, 813, 2153, 2748, 3533, 33, 3132, 6988, 5740,
  -5757, 4045, 4869, 4753, 110, 3866, 2190, 1831, 1896, 99, 99, 9811, 6142]

def fractionalNearFrameSubtreeG2R0139LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0139Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0139LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
