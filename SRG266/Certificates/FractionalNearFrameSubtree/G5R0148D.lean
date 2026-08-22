import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0148`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0148Mask : ℕ := 14237336319134064

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0148Witness : Array ℤ :=
  #[879, 894, -117, 379, -424, -376, 348, -756, 4, 38, -58, -385, 254, -352,
  843, -205, 536, 100, -150, -435, -576, -724, 264, 44, 267, 394, -126,
  -385, 954, 268, 363, -75, -140, -258, 101, -769, -388, 1119, -461, -256,
  -276, -724, -640, 404, 15, 351, 294, -248, -23, -403, -301, -129, 279,
  -30, 619, 820, 161, -128, 882, -158, 321, -13, -664, -191, 759, -208, 180,
  -175, 140, -452, -376, 258, -91, -273, 317, 845, -218, 948, -354, -336,
  261, 0, -144, -326, -33, 46, -410, 162, 850, -91, -837, 231, -428, -434,
  -153, 800, 26, 440, 859, -384, 122, -431, -477, 94, 36, -230, -77, -230,
  393, -135, -199, -705, 322, 865, -425, 90, 567, 254, -577, -670, -50, 151,
  -148, 52, 245, 483, 486, 648, 82, -442, 264, 346, -145, 374, 776, 217,
  686, 427, 110, 135, -5, 153, 931, -607, -793, 877, -97, -1071, 109, -263,
  0, -80, 177, 588, -126, -880, -558, -82, -44, 30, 76, 285, -253, -2, 35,
  263, 484, 405]

theorem fractionalNearFrameSubtreeG5R0148_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0148Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0148Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0148Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0148_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0148LowerBoundTable : List ℤ :=
  [-647, 284, 31, -5, 32, 637, 442, 31, 32, 1643, 99, 1140, 1659, 3753,
  1361, 2321, 799, -1264, 1950, 99, 100, -274, 1715, 100, 99]

def fractionalNearFrameSubtreeG5R0148LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0148Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0148LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
