import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0121`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0121Mask : ℕ := 5827670753927457

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0121Witness : Array ℤ :=
  #[634, -56, 251, 146, -137, 901, 310, 497, 600, -46, 0, 65, -453, -1102,
  -774, -780, 196, 636, 112, 427, 686, -388, -366, -372, -265, 33, -439,
  -456, 91, -200, -547, -214, -211, -127, -110, 298, 399, 359, 579, -275,
  -265, -184, 375, 638, -141, 120, 200, 1141, -149, -140, -118, -1029, -66,
  -947, 820, -146, 455, 43, 85, -319, 445, 94, -654, -257, 174, -5, -548,
  517, 880, -772, -177, 306, 853, 744, -113, -38, -105, 1001, 455, -227,
  -382, 378, 479, -311, 401, 50, -330, 400, -295, 137, 20, 117, 739, 269,
  771, -189, 71, -135, -408, -677, -316, 120, -178, 73, -74, 397, 12, 369,
  -629, -877, -353, 744, -116, 299, 185, -886, 687, 268, -86, 204, -548,
  -357, -1340, 657, -252, 764, -489, -654, 346, -302, -355, -330, -74, 0,
  -188, 544, -252, 532, -41, 434, -329, -211, 136, 400, 1230, 567, 854, 283,
  -680, -460, -936, -8, 8, -81, 270, -567, -432, -83, 652, 188, 203, 298,
  753, -176, 399, 591, 730, 328]

theorem fractionalNearFrameSubtreeG5R0121_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0121Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0121Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0121Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0121_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0121LowerBoundTable : List ℤ :=
  [-247, 496, 314, 32, 524, -767, -135, -235, 1334, -35, 1738, -565, 1458,
  4209, 1707, 926, 291, -1109, 1200, 2941, 99, 100, -1655, 133, 4616]

def fractionalNearFrameSubtreeG5R0121LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0121Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0121LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
