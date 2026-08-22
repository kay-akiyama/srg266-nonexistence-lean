import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0588`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0588Mask : ℕ := 6857193275232872

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0588Witness : Array ℤ :=
  #[1627, 892, 392, -595, 2259, 19, 349, 121, -810, -366, 439, -1360, -1064,
  715, 421, 0, 81, -98, -327, -13, 262, 271, -307, 38, 563, 206, 1601, -85,
  365, -125, 206, 403, 1841, 121, -965, -1176, -1549, 847, 1719, -314,
  -1896, -2469, 159, 269, 602, -406, 75, -611, 33, -1385, -1284, -609, -85,
  122, 296, 295, 664, 1183, 258, -1438, 373, 922, -1091, -1619, -225, -396,
  880, -971, 722, 129, -860, -577, 201, 428, -369, -593, -229, 330, 133,
  777, -1410, 713, 871, -825, 907, 115, -773, 338, -295, 1684, 968, 698,
  -846, -934, -529, -1266, -733, 2450, -57, 262, -704, 871, 1250, 338, 140,
  428, 390, 436, 1111, -405, -296, -580, 1011, 841, 595, -99, -938, -1158,
  -792, 611, -433, 785, -1255, 1, 445, -178, -752, 588, 748, -17, 238,
  -1326, 893, 836, 867, 171, -138, 1827, 1260, 653, 265, 794, -1478, 946,
  459, 1228, 756, 164, -821, 1505, 1088, 774, -653, -473, -955, 420, -117,
  727, -42, 337, 368, -586, 64, -28, 1277, -235, -73, 1463]

theorem fractionalNearFrameSubtreeG2R0588_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0588Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0588Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0588Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0588_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0588LowerBoundTable : List ℤ :=
  [102, 3196, 463, 2488, 32, 232, -349, 33, 873, 4354, 2404, 1873, 99, 1663,
  437, 99, -682, 4797, 6738, 4030, 3444, -1747, -545, -1933, 1667]

def fractionalNearFrameSubtreeG2R0588LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0588Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0588LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
