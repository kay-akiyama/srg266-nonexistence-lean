import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0060`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0060Mask : ℕ := 4979950577640453

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0060Witness : Array ℤ :=
  #[1534, 939, 1240, 1913, 1434, 3256, 296, 910, -24, 109, 608, -3733, 0,
  -2987, -1966, -930, -4620, 769, -1518, 0, 1168, -714, 1826, 2271, 3378,
  -249, -470, -651, -1045, 2813, -701, 3180, 2704, -83, -466, -771, 2408,
  2052, -4822, -2119, -2233, 3347, 5892, 863, 726, 867, -1431, 979, 290,
  -598, -207, 4124, -290, 533, -414, -1097, -375, -127, -1432, 2246, 635,
  26, -2884, -1219, -644, 3213, 2853, 1330, 1117, 1767, 1347, 505, 2307,
  -589, -334, 933, 239, -1647, 1027, -136, 624, 384, -480, 535, 186, -334,
  -136, 1154, -802, 52, 2055, 1360, -1000, 76, -278, -621, 109, -1049,
  -1335, 68, 160, 706, 442, 1529, -1138, 631, -873, -810, -934, -426, 1302,
  992, -474, -1074, -29, -1154, 12, -1272, -803, -756, -779, 402, 1187,
  -1095, 115, 440, 1779, 1593, 0, 831, 440, -1815, 1503, -60, 1041, 315, 52,
  23, 2887, -560, -1974, 2459, 3562, -346, 2223, -2279, 560, 2380, -93, -85,
  1732, 202, -1728, 1033, 61, 1083, -2470, 1954, -3781, -1419, -568, 1113,
  1099, -182, 237, 1347, -1484, -1314]

theorem fractionalNearFrameSubtreeG5R0060_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0060Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0060Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0060Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0060_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0060LowerBoundTable : List ℤ :=
  [560, -565, 4659, 2234, 155, 1915, 3695, 1683, 562, 2655, 3711, 6741, 100,
  -479, -1617, 10955, 3631, 5688, 1999, 11000, 3466, 99, 6667, 7040, 6205]

def fractionalNearFrameSubtreeG5R0060LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0060Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0060LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
