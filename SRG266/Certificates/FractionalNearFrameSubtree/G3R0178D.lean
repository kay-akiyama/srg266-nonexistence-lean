import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0178`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0178Mask : ℕ := 6865886011887122

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0178Witness : Array ℤ :=
  #[-246, 165, 332, 321, 442, 1139, 706, 943, -1396, 527, 835, -741, -67,
  -978, -508, -977, 260, -51, -336, 163, 688, 943, -294, -189, -374, -264,
  11, 681, 939, -544, -57, 241, 560, 158, 323, 149, 1356, 112, -17, -45,
  -123, 278, -476, -443, -417, -69, 181, 588, 137, 433, 726, 8, 23, 305,
  -890, 592, 357, 11, 169, 428, -736, 1567, -4, -905, 66, -875, 302, 1256,
  664, -518, 128, 14, -277, -264, 578, 29, -979, 40, 424, 956, -287, -380,
  -685, -84, -405, -199, 109, 1081, -329, -265, -1197, -209, -104, 185, 775,
  115, 346, -462, -175, -985, -698, -655, 521, -582, 962, -50, -60, 223,
  254, 1196, 0, 306, -462, -431, -664, -1280, -888, 343, -257, -247, -247,
  764, 1460, -1052, -396, -17, -418, -412, 1231, -1426, 571, 666, 485, 917,
  450, 667, -1860, 1000, 1744, 1081, 2314, -543, 2492, -78, 385, -74, 607,
  -469, 916, -398, 1321, -919, 517, -345, -8, -719, -146, 213, 526, 524,
  -205, -377, -123, 62, -107, -309, -397, 659]

theorem fractionalNearFrameSubtreeG3R0178_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0178Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0178Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0178Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0178_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0178LowerBoundTable : List ℤ :=
  [55, 1736, -724, 223, 1595, -202, 1657, 1217, 823, -1877, 5819, 3219,
  2369, -1271, 251, -1405, 9, 119, 838, 834, -435, 257, 4537, 1142, 5969]

def fractionalNearFrameSubtreeG3R0178LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0178Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0178LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
