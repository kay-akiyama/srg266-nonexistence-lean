import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0203`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0203Mask : ℕ := 6880043907634328

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0203Witness : Array ℤ :=
  #[181, -227, 822, 208, -1008, 606, 994, 602, 940, 635, -267, -1133, -269,
  0, 36, 11, -219, 1220, -967, -55, -375, 158, 715, -291, 320, 477, 370,
  188, 399, 1134, -415, -202, -496, 378, 248, -908, 611, -255, 92, 489,
  -514, -158, -592, 108, 1043, -378, -318, 273, 502, -31, -93, -147, -244,
  -1441, 598, 224, 500, 405, -346, 972, -367, -149, 1533, 992, 938, 674,
  213, 462, -1634, -1564, -648, 546, 285, -1835, -1327, 73, -963, 97, 87,
  355, -287, -117, 513, 231, 440, 0, -637, 444, 54, 51, 690, 819, 200, 382,
  819, 258, 921, -389, 654, 929, 598, -67, 66, -533, 104, 504, -65, 314,
  -760, -297, -408, 251, -340, 268, 497, 138, 1045, 995, 936, -574, -165,
  1235, -1021, -1608, -456, -467, 142, 454, 245, 178, 285, -239, -76, 553,
  -27, -495, 373, -13, -619, 198, 64, -128, -293, -86, 334, 250, 54, 371,
  422, 823, 273, 128, 234, 935, -325, 158, -130, -337, 848, 52, -259, -303,
  -28, -181, 169, 134, -120, -757]

theorem fractionalNearFrameSubtreeG3R0203_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0203Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0203Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0203Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0203_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0203LowerBoundTable : List ℤ :=
  [355, 32, 426, 1503, 1601, 353, 538, 432, 537, 3715, -1217, 503, 101, 801,
  867, 924, 558, 2068, 3530, 101, 1478, 2031, 1006, 2133, 3537]

def fractionalNearFrameSubtreeG3R0203LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0203Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0203LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
