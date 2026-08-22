import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0171`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0171Mask : ℕ := 2517622466710128

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0171Witness : Array ℤ :=
  #[427, 332, -265, 305, -479, 1438, 130, 949, 263, -1338, -143, -191,
  -1263, -708, -414, -1342, 1058, 236, -102, 260, 1137, 1926, -2294, 482,
  -588, 602, -300, 752, 301, 560, 1107, 867, 262, 1480, -3233, -2826, 978,
  1490, 2610, -2139, -1040, -1763, 1180, -2355, -369, -734, -1751, -1222,
  2670, 2461, 1155, -1037, -1918, 2461, 2367, 1261, 2280, -4463, 884, -134,
  -2634, -1171, 806, 1403, -2303, 1584, -961, 2216, 2002, -1423, 98, 338,
  997, -396, 814, -291, -19, -566, 630, 867, 682, -1542, 2223, -1052, -302,
  1011, 376, 1490, -369, 193, 407, -1340, 0, -1445, -625, 1845, 1489, 1036,
  856, -147, -226, 649, -1544, -389, -411, 809, 1147, 914, 671, -482, -410,
  1939, -692, -606, -2056, -1824, -1032, -1126, -621, 1391, -901, -1004,
  1304, -1748, -1674, -674, -564, -726, -1828, -593, -1037, 766, 1038, -92,
  2247, 1093, 1347, 957, 1625, -125, 2572, 265, -428, 516, 584, 160, 377,
  -67, 1675, -1020, -477, 185, 1185, -1177, -712, 174, -252, 961, -186, 636,
  1362, 1915, 783, 215, -87, 657, 343, -833]

theorem fractionalNearFrameSubtreeG1R0171_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0171Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0171Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0171Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0171_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0171LowerBoundTable : List ℤ :=
  [-325, 2058, 1591, 890, 724, 31, 792, 983, -2233, -1458, 5354, 99, -4835,
  2321, 6124, 6018, -708, 2712, 100, 8614, 1143, 2745, 4467, -2153, 100]

def fractionalNearFrameSubtreeG1R0171LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0171Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0171LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
