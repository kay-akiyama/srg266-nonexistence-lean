import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0036`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0036Mask : ℕ := 529859690152582

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0036Witness : Array ℤ :=
  #[267, 1342, 1380, 1342, 1108, 1238, -530, 0, -105, -243, 894, 647, -1338,
  -1169, -1134, -383, -621, -1006, -241, -612, -264, -285, 50, -1036, -496,
  -459, -87, 606, 1108, 691, 1310, 1499, -217, -1113, -859, -1368, 166, 483,
  103, 446, 1097, 370, 389, -237, 579, 394, 691, 189, -141, -507, -354, 469,
  0, 252, 54, 23, -96, -887, 140, 994, 232, -735, 1003, 478, -13, -12, -537,
  285, 545, -58, -495, 790, -356, 107, -286, -115, 341, -435, 117, 707,
  -469, 414, 50, 232, 236, 373, -18, -157, -95, 459, -529, 272, 540, -5,
  -59, 1021, -24, 283, 165, 442, -905, 70, 631, 622, 868, -311, 681, -324,
  83, 482, 158, -379, -126, -835, 47, 325, 334, 420, 688, -100, 188, -563,
  -377, -209, 648, 473, 370, -145, 537, 41, 389, 252, -131, 245, -575, -6,
  49, 348, -123, 95, -297, -61, -640, 45, -85, 293, -717, -287, -1080, -420,
  276, 217, -538, -225, 383, 307, -126, -96, 385, -232, -485, 555, 587,
  -711, -50, 194, -192, -13]

theorem fractionalNearFrameSubtreeG1R0036_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0036Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0036Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0036Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0036_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0036LowerBoundTable : List ℤ :=
  [478, -525, 32, 2055, 480, 1242, 32, 182, 852, 99, 1734, -954, 1211, 772,
  982, 1751, 1334, 1154, 764, 2562, 1626, 1884, 762, 99, 2741]

def fractionalNearFrameSubtreeG1R0036LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0036Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0036LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
