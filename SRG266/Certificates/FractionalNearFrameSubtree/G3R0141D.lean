import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0141`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0141Mask : ℕ := 6848277758478986

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0141Witness : Array ℤ :=
  #[318, 371, 24, -247, -133, -29, -239, 55, -151, -387, -452, 340, 544,
  481, 850, 243, -10, 329, 344, 274, 201, 219, 259, 271, 156, 295, -322,
  -423, -493, -624, -353, -285, -142, 347, 157, -102, -61, -163, 4, -16,
  -253, -162, -99, -85, -95, 302, 264, -275, -13, -47, -98, 92, -15, -631,
  -42, 75, -271, 274, 219, -97, -406, 134, -113, 218, 4, 80, -100, 554, 287,
  -150, -376, 70, -25, -40, -224, -267, -7, -362, 622, -424, -76, 345, 540,
  220, 254, -379, 845, 316, 91, 505, -10, 468, 64, 77, -312, 83, -152, -233,
  741, 398, 2, -1, 143, 87, -432, 108, -310, 225, 462, 242, 172, 541, -343,
  -451, -569, 194, 355, -487, -817, -456, -347, 157, 472, -171, 49, -294,
  727, 285, 191, -239, -198, -50, -312, 62, 30, 478, 167, -75, 56, -175,
  -341, -339, 158, -226, 36, -42, -158, -78, 205, 119, 262, -92, 323, -401,
  232, 419, 109, 246, 421, 7, -246, -157, 77, -615, 0, -77, 435, 341]

theorem fractionalNearFrameSubtreeG3R0141_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0141Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0141Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0141Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0141_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0141LowerBoundTable : List ℤ :=
  [-79, 32, 31, 584, 10, 672, 33, -53, 356, 1890, -1250, -709, 762, -621,
  -523, 470, 571, -87, 3064, 1355, 260, 1284, 905, 1550, 435]

def fractionalNearFrameSubtreeG3R0141LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0141Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0141LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
