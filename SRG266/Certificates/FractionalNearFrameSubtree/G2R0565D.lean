import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0565`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0565Mask : ℕ := 6846355491209866

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0565Witness : Array ℤ :=
  #[158, -824, -1292, 1709, -1145, 30, 1039, 1021, 1257, 0, 865, 2778, 785,
  1739, 3263, 0, 1466, -24, 2493, 661, 2937, -1065, 776, 207, 198, 1049,
  1242, 1845, 961, 940, 3190, -1351, -811, 2409, 5039, -519, 3133, -115,
  1645, 239, 291, -2628, 1321, 4049, 2408, 11, -2738, -1520, 2208, 1158,
  -831, -1118, -326, 1309, 1017, 2983, 1683, -838, -2367, -1724, 512, 697,
  -756, 0, -243, -854, -520, 558, -39, 2134, -3066, -98, 2841, -286, 1454,
  2074, -2397, -237, -580, 2651, 1176, 978, -3748, -1115, -2308, 281, 3490,
  1963, 2877, 887, -2252, -2890, -441, -2336, 2508, 1640, 3506, 979, 1121,
  3388, -1129, 2433, -4127, 886, -652, -1046, 1178, -1006, 1276, 2833, 220,
  1938, 18, 1126, 106, -2990, 696, 1424, 2175, 2169, -277, 482, 2178, -1319,
  -940, 4271, 842, 839, 2667, -942, 3692, 1269, -2723, -1662, 4310, 1956,
  -827, -2125, 3009, -427, 2556, 1786, 648, 2176, 2135, 874, -4256, 513,
  1144, -2038, 2761, 299, -1, 1669, -2311, -31, 1045, 8, 1241, 91, 49, 1431,
  535, -2052, -1603, -568, 1732, 1735]

theorem fractionalNearFrameSubtreeG2R0565_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0565Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0565Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0565Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0565_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0565LowerBoundTable : List ℤ :=
  [4331, 6519, 1276, 4747, 8810, 5333, 5668, 13346, 3593, 13237, 3322, 7493,
  14577, 5323, 7341, -2819, 1521, 5731, 15702, 1392, 14405, 5699, 1959,
  3665, 10712]

def fractionalNearFrameSubtreeG2R0565LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0565Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0565LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
