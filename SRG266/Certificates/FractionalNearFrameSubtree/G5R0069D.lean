import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0069`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0069Mask : ℕ := 5049674947469730

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0069Witness : Array ℤ :=
  #[889, -437, -712, -129, 325, -11, 0, 1436, 1873, 312, 241, -235, -982,
  -239, -306, -1448, 1, -773, 333, -467, -193, -517, -518, 901, 226, 322,
  262, 157, -517, 505, 518, 386, -245, -97, -400, -554, 48, -1078, -725,
  -305, 87, 24, 0, 381, 287, 183, -406, -104, 1512, -752, 464, -185, 10,
  418, -37, 162, -359, 612, 630, 45, -464, 239, -115, 334, -86, -1192, -83,
  -602, 375, -513, 687, 59, 20, 167, -275, 800, -427, -55, 10, 789, -624,
  83, 872, -377, 576, -1620, 1020, 26, -226, -970, -52, -549, 444, 163, 379,
  -1467, 181, 597, 236, 456, 49, 125, 747, 1718, -605, -415, -274, 20, 754,
  862, 168, 190, -1148, -413, 645, 1453, 555, 862, -402, -670, 745, -1334,
  2654, 5, -286, -753, -407, 158, 362, 2022, 585, -296, 600, 622, -72, -80,
  -882, 1261, -315, -1369, -1808, -64, -109, -430, 344, 747, 514, -242,
  -563, -67, 1438, -285, -131, 1215, -598, 628, 393, -722, 280, 219, 456,
  246, 247, 540, 832, -358, 897, 287]

theorem fractionalNearFrameSubtreeG5R0069_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0069Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0069Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0069Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0069_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0069LowerBoundTable : List ℤ :=
  [403, 1918, 900, 348, 33, 1548, 1364, 112, 392, 4083, 4135, 2295, -1796,
  253, 1093, -1295, 2249, -338, 2005, 100, 627, -874, 944, -728, 1694]

def fractionalNearFrameSubtreeG5R0069LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0069Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0069LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
