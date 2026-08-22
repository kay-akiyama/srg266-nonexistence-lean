import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0106`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0106Mask : ℕ := 5248712250542744

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0106Witness : Array ℤ :=
  #[193, 453, 672, -2993, -1531, -610, 1371, 909, -298, -1851, 182, 1187, 0,
  -3967, 2920, 1917, 481, 1054, 396, 2018, 1501, -159, 2471, 228, -2991,
  -6678, -5762, -5821, -3464, -1451, 1197, 4, 2640, -1095, 2360, 1286,
  -1755, 1846, -2578, 5519, -97, -2084, 80, 1819, 2709, -162, 619, -227,
  -474, -512, -4692, -1311, -1304, 737, 1797, -238, -2341, 5443, -3096,
  -3421, 438, 3434, -6039, 4131, -5212, 2990, 5760, 7851, 0, -1309, -1058,
  -1803, 960, -2452, 6780, -513, 1103, -2241, -2178, 7404, 954, 407, 2069,
  -3247, 639, 838, -1611, -3394, -2420, 198, -29, 1681, -1851, 1518, -1411,
  -1472, -2143, -3778, 24, 901, -449, -1054, 505, -1604, -878, -481, 646,
  -2481, 1380, 3179, 693, -8, -51, 509, 2193, 516, 478, 987, -1366, -5198,
  -1568, -1359, 1313, 1428, 1874, 3452, -2583, -3639, 0, -1366, -4214, 507,
  1686, 957, 2967, -4444, -340, -2458, -3474, 847, 4114, 805, 837, -566, 33,
  -1820, 2720, -3687, 334, 940, 853, -654, -799, 326, 2823, 3883, -4621,
  624, 4127, 1986, 1930, -1273, 970, -785, 7483, -435, 3058, 2403]

theorem fractionalNearFrameSubtreeG3R0106_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0106Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0106Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0106Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0106_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0106LowerBoundTable : List ℤ :=
  [-5227, 2913, 2054, -3813, 2337, 32, 3596, -664, -5094, 7646, -42, 2114,
  -3589, 8658, 100, -85, -4914, 2403, -1296, 6397, -13825, 2165, 8017, 4519,
  908]

def fractionalNearFrameSubtreeG3R0106LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0106Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0106LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
