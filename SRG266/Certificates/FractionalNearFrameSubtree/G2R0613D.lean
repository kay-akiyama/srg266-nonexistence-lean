import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0613`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0613Mask : ℕ := 9586336840927753

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0613Witness : Array ℤ :=
  #[-245, -196, 123, 107, -131, 276, -110, 0, -450, -686, -352, -713, -35,
  397, 87, 38, 1545, 0, 507, 223, 287, -45, 151, -447, -415, 409, -69, -532,
  -348, -760, 356, -1009, -282, -96, 100, -261, -677, 415, 584, 596, -214,
  -182, -23, 369, 489, -233, -56, -58, 172, -53, 554, 217, -350, -599, 21,
  52, -151, 1149, 165, 102, -282, 142, 146, -117, 34, -94, -608, -39, 335,
  278, -354, -112, 180, -461, -30, 684, -936, -509, -323, 114, 207, 227,
  110, 357, 179, -339, 915, 122, -294, 20, -229, 154, -109, 386, 535, -656,
  -243, 54, -42, -4, -7, 223, -80, 13, 46, -615, 587, 644, 305, -158, -136,
  -366, 329, -136, 313, 307, -74, -76, -265, -331, 167, -721, -367, -77, 96,
  -296, 186, 1060, 376, 254, -102, -104, -1533, 482, 91, -295, 561, -328,
  206, -431, -852, 207, 29, -940, 496, 388, 521, 413, 641, -1228, 859, 649,
  -15, -230, 165, 414, -74, 1414, -919, 43, 14, 183, 106, 51, 729, 1406,
  -1261, -1331]

theorem fractionalNearFrameSubtreeG2R0613_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0613Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0613Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0613Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0613_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0613LowerBoundTable : List ℤ :=
  [-289, 32, 32, 862, 32, 398, -762, -188, 32, 2528, -2286, 101, 388, 1260,
  432, 1319, -1388, -211, 99, 2362, 100, 917, -1635, 186, 157]

def fractionalNearFrameSubtreeG2R0613LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0613Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0613LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
