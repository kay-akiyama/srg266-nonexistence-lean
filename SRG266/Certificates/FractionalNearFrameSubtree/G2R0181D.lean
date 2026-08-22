import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0181`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0181Mask : ℕ := 1387774538663000

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0181Witness : Array ℤ :=
  #[405, -2448, -1633, -1190, -879, 543, 993, -196, -229, -509, 630, 1846,
  2428, 657, 1769, 146, -519, 2099, 1152, -407, 626, -790, -1316, -237, 381,
  569, -984, -1503, 672, 1336, 904, 2626, -545, -126, -813, 75, -1195,
  -1576, 130, -1857, -1691, -843, -1397, -9, 610, 535, 99, 1344, 1092, 1081,
  -143, 678, -1798, 1260, -1952, 31, 929, 1147, 984, -55, 623, 811, 825,
  1574, -529, 290, 515, -979, -1376, 719, -86, 165, 2073, -1440, -75, -855,
  2253, 936, 510, -1073, -173, -1082, 2064, -848, 887, -94, -268, 808,
  -1089, 2049, -2047, 1809, -674, -1488, -228, -332, -1683, 24, -1371, 694,
  491, -2427, -460, -726, 222, 337, 575, -533, -1124, -1327, -287, -826,
  1309, -432, 322, 943, 1557, 1077, -991, -1119, -1673, 718, -2732, 42,
  1304, 64, 2183, 1174, 943, 1132, 176, 532, 912, 314, -248, 338, 1557,
  -769, 633, 1042, 296, 1106, -382, -270, 587, 1620, 850, 1493, 1603, 1324,
  0, -1203, 126, -254, -1396, 614, -773, -1644, -1997, -548, 2415, -356,
  1919, -886, 1541, 299, 739, 40]

theorem fractionalNearFrameSubtreeG2R0181_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0181Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0181Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0181Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0181_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0181LowerBoundTable : List ℤ :=
  [-704, 2511, -707, -402, 1684, 2734, 2130, -1033, -1307, 8361, 4941, 1157,
  100, 2889, 4350, -5791, -3129, 5013, -1518, -2168, 5844, 6194, 6922, 2164,
  100]

def fractionalNearFrameSubtreeG2R0181LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0181Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0181LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
