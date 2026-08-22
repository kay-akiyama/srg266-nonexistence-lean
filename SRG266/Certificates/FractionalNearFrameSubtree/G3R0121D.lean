import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0121`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0121Mask : ℕ := 5389585021967024

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0121Witness : Array ℤ :=
  #[124, -662, 180, 986, -278, 289, 1633, 1195, -250, -247, 1434, -594, 334,
  -537, 1, -83, 320, 29, 923, 144, 18, 1875, -384, -32, 530, 688, -384,
  1098, -1, 1224, -731, -48, 219, 1066, 2555, -2315, -1632, -143, 619, 1764,
  167, 1021, 1749, 2244, -311, -1101, -432, -683, -878, 1640, 292, 223,
  -255, 721, -472, 258, 205, 108, -546, -380, 550, -7, -1974, 556, 1281,
  509, -1134, -1139, -1584, 937, 501, 259, 248, 66, -236, 227, 108, 350,
  694, -717, -876, -450, 502, -1747, -1388, -1125, -327, 578, 290, 2172,
  1424, 1174, 658, 688, -1264, 1985, 52, -523, -1482, 1935, -210, -86, 1037,
  -180, -42, 644, -427, 835, -1488, 1364, 1992, 1031, -307, 2, 543, -327,
  1815, 753, 2657, 1153, -2169, -544, -352, 333, -4105, -410, -1366, 593,
  711, 1289, 872, 1504, 212, 0, 301, -1627, 835, -234, -1151, -231, 826,
  130, 512, 2163, 2350, 796, 329, 1175, 452, -403, -206, 1651, -460, 296,
  -833, -1498, -610, 1122, -967, 681, -710, 1385, 20, 241, 934, -689, -2329,
  0]

theorem fractionalNearFrameSubtreeG3R0121_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0121Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0121Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0121Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0121_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0121LowerBoundTable : List ℤ :=
  [1188, 2224, 1552, 32, 2382, 2425, 31, 3446, 2110, 6473, -567, 6845,
  -1638, 4734, -4342, 3305, 3992, 175, 5105, 5060, -1488, 3918, 2738, 4434,
  1171]

def fractionalNearFrameSubtreeG3R0121LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0121Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0121LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
