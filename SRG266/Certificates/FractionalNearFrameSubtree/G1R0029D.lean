import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0029`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0029Mask : ℕ := 468286464171025

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0029Witness : Array ℤ :=
  #[1270, -3361, -1700, 0, -587, -1611, 1487, -1124, -321, 51, -577, 2389,
  0, 487, 1179, 1640, 2539, 1127, 309, 3026, -1507, 614, -2098, 314, -4025,
  -1337, -2465, 222, 2534, 641, -278, 1482, -160, -1929, 424, 233, -202,
  3820, 1038, 740, -59, -3489, 1509, 25, 991, 31, 301, 0, 1461, -681, -765,
  1325, 790, 2165, -771, 473, -1963, -2074, 429, -501, 4585, 3614, 2023,
  -114, 456, 1856, 2341, 2338, 2593, -20, 85, 2142, 1929, -200, -563, 2343,
  3113, 1465, 0, 1139, -888, 1295, 893, 2384, 344, 178, -40, 66, -768, 499,
  1060, 147, 2378, 3817, -930, 1953, 2691, 269, -839, -2478, 2863, 1154,
  1087, 1028, 684, -348, 245, -1098, -815, 3365, -1260, -1855, 469, 1030,
  -1871, 971, -2195, 702, 1029, 823, 2734, -578, 1899, 1573, -787, -4678,
  -1295, 1445, -1592, -2997, 831, 2354, 3511, 186, 1078, -544, 435, -773,
  -2158, -1009, 1708, -817, 308, -856, 329, -3314, -55, 2902, -208, 160,
  -1300, -97, -1050, -2494, 3468, -297, 2378, -124, 1469, 3521, 3100, 788,
  1509, -1014, 3164, -1608, -2502, -3069]

theorem fractionalNearFrameSubtreeG1R0029_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0029Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0029Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0029Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0029_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0029LowerBoundTable : List ℤ :=
  [2462, 412, 6523, 4608, 2094, 3345, 2713, 4855, 5525, 2849, 174, 3433,
  1922, 6050, -2346, 14048, 5039, 8239, 2376, 4108, 12886, 5768, 8198, 4051,
  2993]

def fractionalNearFrameSubtreeG1R0029LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0029Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0029LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
