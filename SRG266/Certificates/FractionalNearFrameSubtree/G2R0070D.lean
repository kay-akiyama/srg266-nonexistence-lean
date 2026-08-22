import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0070`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0070Mask : ℕ := 957317351588514

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0070Witness : Array ℤ :=
  #[-224, -97, 310, 370, 793, 515, -26, -6, -264, -229, -130, -626, -66,
  -331, 0, -231, -963, -789, -327, -632, -50, 409, 289, 406, 147, -201, 340,
  276, -69, 255, -324, -409, -150, 254, 179, 235, 382, 526, 189, -330, 802,
  244, -343, 32, 117, 95, 302, 250, 381, 119, 510, 388, -118, 201, -510,
  -104, -244, 139, 5, 297, 601, -393, 366, 230, -273, -108, -184, 89, 118,
  -136, 331, -179, 153, -69, 328, 419, -255, 212, -277, 121, 239, 14, 256,
  -210, 414, 151, 86, 429, -204, -283, 3, 300, -523, -232, -162, 135, -76,
  -270, -191, -160, -526, -360, -23, -72, -160, -274, -174, -172, -74, -155,
  48, 46, -418, -111, 0, -52, 99, 141, 2, 181, -619, -230, -52, -195, -666,
  -365, 150, 287, -316, -57, -255, -30, 98, -178, -171, 0, -464, 159, -64,
  482, 78, -16, 201, -425, -176, 252, -203, -511, 466, -205, -342, 301, -64,
  60, 125, 188, 229, -368, 606, -341, -207, 382, 485, 93, 385, 39, 348,
  -240]

theorem fractionalNearFrameSubtreeG2R0070_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0070Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0070Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0070Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0070_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0070LowerBoundTable : List ℤ :=
  [-586, -186, -39, -313, -207, 164, 223, -374, 95, 100, 98, -1419, -552,
  104, 1046, -248, 2534, 418, 1420, -765, 740, -453, 1097, 285, -53]

def fractionalNearFrameSubtreeG2R0070LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0070Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0070LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
