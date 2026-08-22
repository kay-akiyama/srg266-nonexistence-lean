import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0338`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0338Mask : ℕ := 5645687167035913

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0338Witness : Array ℤ :=
  #[-860, -528, -951, -820, -1753, 282, -325, 939, 494, -71, 927, 207, 363,
  -29, 671, 935, 889, 0, 33, 1113, 1395, 514, 765, -1625, 291, 907, 102,
  -96, -599, -904, -1532, -121, -684, -656, -521, -1257, 322, 132, 1311,
  603, 264, -286, 144, 754, 1109, -257, 0, 241, -631, 13, 631, -573, -248,
  407, 299, 313, 1081, 745, -262, -659, -370, 936, 120, -161, 351, -74, 172,
  607, -1002, 0, 1459, -150, 707, -276, 373, 157, 55, 806, 191, 403, -492,
  410, 711, 195, -337, 114, 312, 460, 740, 51, 456, 262, 278, 549, 286, 481,
  522, 686, 128, 158, 291, 798, -228, 248, 12, -3, -644, -395, -164, 142,
  -146, -495, 414, -871, 70, -19, -137, 55, -215, 1344, -1, -287, 431, 164,
  -8, -315, 346, 38, -45, -170, -505, 578, 829, -375, -206, -302, -171,
  -481, 28, -266, -22, 213, 611, -552, 370, -856, -522, -458, 805, -159,
  -341, -166, 387, -28, 42, -642, 776, 111, -23, 546, -239, -534, -828,
  -431, -626, -37, -390, -1670]

theorem fractionalNearFrameSubtreeG2R0338_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0338Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0338Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0338Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0338_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0338LowerBoundTable : List ℤ :=
  [156, -1384, 358, 780, 33, 277, 751, 32, 644, 2737, -2029, -890, 1119,
  650, -952, 2192, 200, 1446, 2780, 2441, 3211, 2428, 2496, 2509, 967]

def fractionalNearFrameSubtreeG2R0338LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0338Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0338LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
