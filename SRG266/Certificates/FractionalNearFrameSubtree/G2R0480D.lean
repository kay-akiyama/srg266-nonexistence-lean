import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0480`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0480Mask : ℕ := 5810338772468370

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0480Witness : Array ℤ :=
  #[-25, 396, 5, 395, -453, -75, -664, 330, -198, 303, 288, -241, 346, -80,
  -253, -649, -252, 229, -215, 215, 54, -888, 193, 394, 42, -83, 308, 302,
  147, 459, -171, -263, -51, 735, 429, 104, 248, 49, 190, -47, 203, 517,
  193, 331, 227, 112, 717, 278, -210, -186, 63, -242, -21, 141, -34, -486,
  -445, 151, -2, 306, 13, 550, 334, -150, 226, -550, 553, 100, 288, 221,
  161, 371, 420, -97, -396, -99, -25, 167, 463, 114, 168, 0, -272, -116,
  285, 498, 94, 165, 247, 367, 375, 335, 605, 551, 151, 634, -10, 109, -67,
  435, 143, -150, 33, 408, -208, -854, -772, -646, 225, 422, 507, 325, 465,
  193, 224, 78, 106, -81, -309, -67, 145, -126, 174, -170, -16, -436, -215,
  -53, 122, 114, 287, -74, 214, 73, -262, 245, 31, 29, 266, -141, 342, 242,
  -292, 217, -134, -123, -213, 62, 421, -51, -328, 256, 481, -327, -404,
  924, -169, -153, 47, 198, 333, 256, 716, 202, 308, 460, -430, -325]

theorem fractionalNearFrameSubtreeG2R0480_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0480Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0480Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0480Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0480_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0480LowerBoundTable : List ℤ :=
  [728, 713, 1151, 2, 1681, 917, 676, 816, 837, 1377, 54, 1347, 170, 2168,
  82, 156, 2945, 1775, 1689, -299, 406, 1369, 1468, 1587, 803]

def fractionalNearFrameSubtreeG2R0480LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0480Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0480LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
