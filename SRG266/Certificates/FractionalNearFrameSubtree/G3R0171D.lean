import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0171`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0171Mask : ℕ := 6862864242380298

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0171Witness : Array ℤ :=
  #[214, 350, 2261, 1374, 3366, 2333, -1082, 424, 0, 595, 1155, -3734,
  -2334, -1069, -880, 1591, -1574, -1565, 678, 580, -288, -1011, 211, 2296,
  -893, 216, -95, 1274, 1704, 4655, -1344, -1591, -1223, 604, 1647, 778, 92,
  182, 656, -1484, 275, 1644, -570, -454, 475, 605, -656, -967, -747, 1056,
  96, 1247, -1260, 1209, 694, 388, -429, -640, 1359, 831, -395, 14, 1377, 9,
  56, -571, -298, 194, 333, 1096, 156, 998, -817, -599, 667, -1443, -336,
  -428, -1178, 1714, 1356, -393, 273, 20, 459, 518, -172, 150, -135, 1019,
  299, 824, -273, -239, 365, -519, 197, 787, -1358, 1023, 3, -1058, 1068,
  925, 856, 891, 817, -561, -468, 300, 8, 2117, 1339, -419, 924, -375, 3864,
  2612, 3710, -1556, -366, -1841, -3042, 37, -20, -1436, -1541, -332, -585,
  1208, 2045, 1478, 77, 301, -1612, -978, 464, 149, -493, -1316, 1702,
  -1307, 370, 1057, 311, -122, -753, -497, -911, 825, 1700, -631, 1994,
  -715, 147, -565, 433, -1287, 1429, 181, 250, 1075, 2296, 462, -1165, -803,
  -540, -4225]

theorem fractionalNearFrameSubtreeG3R0171_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0171Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0171Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0171Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0171_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0171LowerBoundTable : List ℤ :=
  [134, -493, 33, 3388, 369, 2482, 1184, -1177, 2607, 12918, -490, 1830,
  100, -2859, -1608, 3573, 1147, 4402, 12536, 2445, 9479, 3749, 1897, 5398,
  100]

def fractionalNearFrameSubtreeG3R0171LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0171Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0171LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
