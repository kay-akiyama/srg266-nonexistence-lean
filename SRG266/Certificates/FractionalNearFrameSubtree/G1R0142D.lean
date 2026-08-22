import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0142`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0142Mask : ℕ := 1039465419751640

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0142Witness : Array ℤ :=
  #[-936, -473, -1489, -3300, -2143, 3000, 2538, 2270, 986, 4081, -1552, 0,
  -848, -1683, 785, 1082, -1509, 1238, -1253, -296, -237, -1357, -3316,
  -388, 1939, 2335, 1504, 574, 149, 0, -24, -7, 966, -1621, 1723, 1064,
  -1927, -2755, 0, 3424, 211, -1316, -1035, -2018, -311, 5089, 1196, 0,
  -1528, -1608, 63, 3268, -1036, 1864, -914, 139, 1917, -673, 1267, 1201,
  1935, 452, -1073, -966, 253, 2477, -1977, -753, 1482, -102, -2619, -1204,
  -552, -91, 1393, 269, -1478, 335, -394, 1518, 2337, -336, 3097, 476, 118,
  2410, -574, -32, 1266, 1776, 308, -441, 1018, -14, 985, 805, 988, -1043,
  1574, 1801, 360, -1104, 741, 1564, -81, 2353, 288, -1072, -1819, -2415,
  -564, 1617, 2703, 683, -2583, 340, -1338, -116, 2685, -609, -742, -609,
  -229, -429, 340, -1863, 203, -3160, 448, 1264, -130, -3163, 1222, 0, 935,
  -2989, -601, -105, -786, 4096, 543, 2727, -1195, -1262, -2298, -844, 169,
  -133, 354, 1505, -199, -1196, 1366, 2041, -2085, 1922, 1521, -3409, 633,
  -1873, -986, 3074, -176, 4205, -1720, 401, 3058, -3424]

theorem fractionalNearFrameSubtreeG1R0142_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0142Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0142Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0142Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0142_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0142LowerBoundTable : List ℤ :=
  [-737, 32, 3415, 32, 687, 579, 3864, 33, 726, 4615, -8805, -823, 274,
  5205, 5359, -3692, 4919, 5667, 4417, 7351, 2166, 4902, 1934, 7847, 718]

def fractionalNearFrameSubtreeG1R0142LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0142Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0142LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
