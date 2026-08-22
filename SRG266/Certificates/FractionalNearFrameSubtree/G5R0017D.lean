import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0017`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0017Mask : ℕ := 1039265905475651

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0017Witness : Array ℤ :=
  #[-2344, -1864, -1763, -1668, -1974, -168, -1206, -675, -2229, -1198,
  -139, 2348, 2445, 1498, 1460, 2443, -900, -506, -331, -448, -527, 60, 833,
  513, 37, 93, 1026, 1167, 809, -1093, -1785, -2139, 984, -1680, -684, -579,
  -995, -3001, -136, 0, 845, 916, 1873, -303, -1977, -699, 71, 0, 0, -2494,
  -1273, 914, 402, 730, 225, 855, 884, 514, -340, 367, 809, 458, -296, 195,
  -158, 350, 1724, -217, -12, 508, -467, -1190, 30, -220, 208, -732, 432,
  -618, -19, -1223, -255, 548, 1087, -1153, 202, 778, 250, 403, 1069, -1412,
  1508, -1024, 51, 674, 745, -97, -126, -141, -345, 1387, 495, 78, -122, 41,
  527, 72, -530, 768, -1464, -1646, 430, -371, -152, 72, -608, -932, 316,
  -1423, -901, 1714, -195, -282, 209, -61, -472, -159, -288, -162, 160,
  -584, 466, -48, -603, -524, -607, 2911, 954, -461, 2603, 1935, 0, 1085,
  1201, -1751, 2423, 670, 1093, 2697, -1830, -88, 131, 1642, -1597, -1207,
  -602, -941, -807, -853, 711, 870, 1756, 494, 774, 580, 429, -1003, 758,
  -1027]

theorem fractionalNearFrameSubtreeG5R0017_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0017Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0017Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0017Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0017_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0017LowerBoundTable : List ℤ :=
  [-1834, 2295, 32, 369, -1244, 32, -3025, 1321, -1322, 2137, -335, 3782,
  968, 2798, 1417, 2106, -1135, 2612, -762, -1380, 101, -5764, -4594, 4533,
  -790]

def fractionalNearFrameSubtreeG5R0017LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0017Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0017LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
