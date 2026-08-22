import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0028`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0028Mask : ℕ := 953959761679878

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0028Witness : Array ℤ :=
  #[-602, 333, -632, 449, -858, -524, -755, 913, -819, -1192, -445, 1122,
  1789, 848, 0, 289, 516, 2039, 1396, 1893, 1272, -303, -521, -273, -370,
  -143, -434, -1411, -1387, -1667, -1009, -133, 66, -896, -746, 185, 97,
  151, 267, 895, 1231, -736, -437, 1428, 482, 421, 98, 962, 886, -3074,
  -355, -102, 448, 576, -638, -583, 957, 409, -594, 0, -667, -208, -376,
  357, 1037, -29, -730, 214, -483, 990, -490, -504, 290, 420, 2040, -19,
  -298, -480, 1123, -422, -374, 874, -1048, -1163, 459, 1646, 585, -183,
  -2779, 13, -79, 1531, 1136, 736, 324, 265, 178, -88, -2670, -388, 158,
  1216, 175, 369, 1340, 1337, -612, -146, -497, 729, -261, 1167, -352,
  -1348, -660, -167, 1891, 70, 645, -899, -334, 704, -79, -819, 2058, 307,
  -613, 152, 541, 356, 30, -1228, 2400, 1623, -1580, 764, 1261, -2734, 1000,
  -103, 428, -115, 598, 1328, 437, 1008, -87, 179, 188, 925, 929, 505, -28,
  -484, -689, -1207, -2098, 291, 395, 979, 1186, -567, 386, 2011, 688, 89,
  833, -1412]

theorem fractionalNearFrameSubtreeG3R0028_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0028Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0028Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0028Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0028_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0028LowerBoundTable : List ℤ :=
  [489, 1932, 1899, 1273, 31, 1447, 846, 1857, -1535, 3386, 3198, 2514,
  1384, 3660, 4600, 3108, 2728, 84, -202, 87, -459, 665, -275, 2206, -624]

def fractionalNearFrameSubtreeG3R0028LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0028Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0028LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
