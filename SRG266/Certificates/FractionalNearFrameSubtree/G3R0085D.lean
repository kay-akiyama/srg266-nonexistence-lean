import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0085`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0085Mask : ℕ := 2479047711560338

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0085Witness : Array ℤ :=
  #[1015, 705, 537, -207, 280, 759, 26, 33, -615, 0, -187, -746, -521, -812,
  -341, -294, -177, -762, -811, -679, -748, 161, -283, 343, 14, 305, 1103,
  914, 286, 491, 371, -592, -423, 346, 167, 322, 621, -134, 505, -360, 156,
  471, 16, -347, -430, -301, 379, -246, 483, -1, -191, 421, -206, 422, 58,
  -349, 512, -449, -62, 63, 275, -148, 245, -599, 120, 530, 436, 233, 221,
  -697, 210, 474, 65, -1029, 660, 670, 5, -43, -386, 822, -42, 275, -303,
  638, 290, 108, -1038, -158, 50, 222, 78, 43, 84, 720, 148, 72, 696, -1109,
  -613, -18, -651, -55, 385, 373, -314, 654, -368, -115, 859, 820, -778,
  -1131, -397, -87, 261, -833, 14, -139, -62, -166, -748, 507, -181, -646,
  -233, 543, 18, 135, -9, 537, 237, 20, -716, 482, 465, 78, 347, 591, 654,
  492, -394, -504, 399, 778, -431, -196, -43, 13, 56, 98, -436, 451, -625,
  267, -53, 502, -31, -58, -25, -462, 752, -319, -169, -350, 334, -628, 0,
  357]

theorem fractionalNearFrameSubtreeG3R0085_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0085Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0085Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0085Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0085_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0085LowerBoundTable : List ℤ :=
  [-736, 31, -221, 419, -1076, -213, 675, 728, 217, 1492, -349, 248, 142,
  101, 2275, 579, 303, 2123, 683, 582, 63, 170, 1716, 191, 2792]

def fractionalNearFrameSubtreeG3R0085LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0085Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0085LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
