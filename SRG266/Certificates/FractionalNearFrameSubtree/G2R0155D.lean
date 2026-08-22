import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0155`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0155Mask : ℕ := 1378528433897698

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0155Witness : Array ℤ :=
  #[53, -254, 885, -1506, -1197, 246, 1286, 360, 1174, 336, 1977, 0, -623,
  -808, 501, -586, 64, 1764, -68, 11, -1981, 1127, -340, 241, 579, 551, 282,
  396, -425, -277, 524, 1727, -1217, 428, 879, -1901, -1115, 181, -829,
  -351, 240, -859, 446, 1401, 5, -2626, 719, -801, 471, 2043, 1123, 446,
  1176, -712, -230, -240, -1453, 718, -173, -582, 1164, 916, 111, 989, -145,
  459, 772, 653, -626, 93, -577, -720, 859, 277, 1050, -482, 610, 345, -230,
  -163, 2293, 2153, 1115, 2528, 1855, -790, 676, -291, 308, -211, 428, 435,
  665, 329, 516, -264, 476, -1328, 634, 128, -154, 573, 505, 719, 1465,
  1242, 1772, 1458, -195, -901, -780, -1243, -752, -1593, -550, -320, -733,
  -856, 450, -1005, 829, 937, 5, -148, 265, 408, 1080, 476, 2184, -399, -15,
  66, 80, -114, -799, -399, -833, -1326, 1107, 1687, 443, -936, -508, 704,
  -899, 173, -1756, -1531, -259, -1186, 331, 1230, 2070, 0, 454, 233, 144,
  437, 59, 241, -1160, -525, 1040, -676, 99, 663, 607, 1327]

theorem fractionalNearFrameSubtreeG2R0155_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0155Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0155Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0155Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0155_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0155LowerBoundTable : List ℤ :=
  [393, 33, 3684, 3782, 639, -1191, 899, 1198, 1928, 117, -3332, 1919, 3530,
  6899, 6286, 3918, 5780, 4127, 7469, 310, 3997, 1839, 3198, -2002, 100]

def fractionalNearFrameSubtreeG2R0155LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0155Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0155LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
