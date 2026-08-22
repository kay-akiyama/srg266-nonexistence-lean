import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0390`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0390Mask : ℕ := 5739952991584650

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0390Witness : Array ℤ :=
  #[-928, -260, -464, -940, -1176, 362, 326, 640, 9, 373, 358, 141, 0, 875,
  -150, 365, 387, 384, 122, 131, 1001, 58, -187, 338, 1, 593, -169, -1378,
  -507, 189, -365, -895, -610, 546, -160, 937, 1566, 185, -485, -1435, 1107,
  940, 237, -184, -143, -149, 1925, 913, 226, -795, 1326, 665, 851, -237,
  -895, -1261, -975, -703, -345, 753, -669, 19, 5, 56, -127, 924, -49, 539,
  -355, 116, 430, -41, -130, -335, 104, 908, -613, 514, -150, 31, 1111,
  -264, 161, -116, 497, -476, 1166, -56, 334, 1082, -8, 611, -229, -256,
  890, 87, 427, -495, 533, 233, 480, 340, 665, -598, -670, -187, -776, -207,
  -345, 74, 735, 861, 158, -893, -381, -887, -11, -124, 231, 522, 311, -291,
  129, 88, -384, 1419, -454, -270, 419, -530, -263, -35, 27, 252, 988, 633,
  -138, -530, 319, -573, 343, 751, -1098, -660, -1002, 266, -538, 221, 217,
  296, -486, -324, 307, 134, 278, 638, -247, 6, 80, 462, 632, -348, 667,
  327, 179, 241, 715, 618]

theorem fractionalNearFrameSubtreeG2R0390_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0390Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0390Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0390Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0390_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0390LowerBoundTable : List ℤ :=
  [85, 681, 64, 433, 645, 1608, 98, 493, 707, 2340, 1303, 742, 99, 1717,
  -1595, 2131, 754, 3706, 1850, -613, -354, 3334, 4336, 2791, 2246]

def fractionalNearFrameSubtreeG2R0390LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0390Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0390LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
