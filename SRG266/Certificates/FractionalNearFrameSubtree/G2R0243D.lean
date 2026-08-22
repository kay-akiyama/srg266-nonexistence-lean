import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0243`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0243Mask : ℕ := 5161779494867724

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0243Witness : Array ℤ :=
  #[875, -148, 780, 877, -69, -13, -202, 204, 361, 225, 923, -783, -1171,
  -37, -392, -102, -682, 585, -25, 276, -830, 30, 59, -244, 185, 837, 70,
  -261, 613, -303, 958, 1205, 437, 652, -26, 5, -999, -937, -458, -155,
  -245, -64, -1301, 108, -1112, -473, -228, -787, -210, 887, 167, -8, -377,
  123, -38, 1463, -70, 232, -209, -771, 93, 856, 308, 35, 80, -286, 7, 89,
  -153, 1099, 1053, 559, -18, -1154, 454, -1693, -878, 677, 86, -585, -282,
  92, -684, 645, -480, 197, 440, 494, 378, 1384, 445, -345, 247, -614, -353,
  133, 619, 178, 62, 280, 228, 452, 364, 1, 199, 420, 42, -252, -311, -151,
  -366, -190, 0, 741, -137, -439, -228, -306, -70, -200, 310, 570, 60, -124,
  -779, -659, 270, 434, 209, 498, -188, 488, 223, 234, -792, 701, -358, 815,
  -12, -131, 858, 38, -477, 731, 237, -210, -360, -270, -530, 276, 46, -971,
  -244, 385, 407, -7, 129, 51, 305, -995, 669, -473, 649, 309, 637, -22,
  -179, -232]

theorem fractionalNearFrameSubtreeG2R0243_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0243Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0243Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0243Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0243_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0243LowerBoundTable : List ℤ :=
  [-485, -236, 32, 1462, 165, 31, -211, 758, -359, -904, 1258, 2113, -1118,
  426, 3065, -291, 2283, 2664, 440, 3655, 748, 840, -2320, 634, 1185]

def fractionalNearFrameSubtreeG2R0243LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0243Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0243LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
