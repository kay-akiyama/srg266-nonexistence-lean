import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0022`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0022Mask : ℕ := 1077025640972870

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0022Witness : Array ℤ :=
  #[758, 1593, 854, 510, -944, 482, -821, -371, 712, -703, -303, -537, 492,
  732, 0, 651, 586, -1098, -1248, -183, -1124, 812, -447, -271, 475, 163,
  -811, 1027, 205, 2195, 997, 992, 647, 546, 490, -325, 90, -625, -97, -13,
  -182, 60, -260, 183, 388, -216, 246, -122, -964, 0, 212, -577, 112, 725,
  1176, 1394, 903, -1482, -510, 726, 185, -711, 1130, -596, 791, -834, 888,
  -924, 157, 520, 440, 111, 598, 1199, -789, -312, 859, 229, 1343, 1278,
  -504, 258, -81, 1299, 427, 146, 4, -479, 573, -159, 110, 670, 10, 981,
  119, 1140, 15, 841, 555, 533, -313, 30, 1416, 327, 0, 1747, 623, 548,
  -548, 648, -239, 940, 204, 1026, -1232, -263, 81, -453, -94, 90, -168,
  -72, 0, 159, -55, 998, 1080, 418, -221, 1246, -136, -253, 1283, -401, 221,
  -366, 1212, -878, -473, -421, -584, -744, 209, -1019, 702, 126, 806, 343,
  1133, 106, -120, -466, -36, 346, 703, 53, 1032, -286, 1316, 178, 998, 160,
  -326, -1254, -1555, 270, 100, 0]

theorem fractionalNearFrameSubtreeG5R0022_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0022Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0022Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0022Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0022_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0022LowerBoundTable : List ℤ :=
  [1214, 477, 2122, 2575, 1887, 2349, 2551, 3136, 1541, 4904, 2707, 100, 99,
  1061, 5714, 3461, -209, 4727, 2122, 3395, 2169, 2695, 4982, -3910, 4451]

def fractionalNearFrameSubtreeG5R0022LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0022Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0022LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
