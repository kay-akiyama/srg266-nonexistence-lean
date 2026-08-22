import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0429`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0429Mask : ℕ := 5784362811036306

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0429Witness : Array ℤ :=
  #[-413, 298, -18, 157, 814, -402, 371, 698, 759, 680, 1431, -1223, -724,
  -211, -71, -1460, -1117, -44, -417, -224, -168, -504, -1093, 501, -152,
  167, 748, 732, 1375, 1145, 795, 1584, -482, 0, 10, -936, -876, 738, 722,
  745, -149, 15, 858, 431, 677, 1490, -584, -659, -458, -809, -354, -658,
  76, 789, 611, -336, -916, 107, 225, -597, 516, 414, 814, -296, 317, -858,
  -1020, 243, -187, -321, 523, 215, 363, -179, 581, 302, 36, -282, -182,
  -19, 993, 429, -123, 158, -101, 392, 963, -694, -236, -869, -727, 528,
  789, 4, -1525, 1121, 629, 308, 619, 752, 485, 202, 688, 485, 204, -217,
  -75, 804, -985, -388, -197, 168, 1241, -23, -312, 101, 19, -770, -221,
  -114, 1108, 635, 1206, -236, -249, -164, -48, -106, -429, -17, 386, -91,
  -72, -200, 303, 1625, -132, -503, 35, -618, 860, 507, -15, -370, 0, -568,
  -523, -283, -803, -166, 609, -25, -284, -430, 920, -17, -722, 640, -445,
  211, 573, -535, 324, 324, 805, 125, -1571, -452]

theorem fractionalNearFrameSubtreeG2R0429_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0429Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0429Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0429Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0429_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0429LowerBoundTable : List ℤ :=
  [185, 260, 1593, -400, 846, 688, 270, 544, 308, 9, -723, 10, 213, 2918,
  3404, 3385, 3489, -1004, 1841, 774, 1574, -1995, -1227, 1287, 4279]

def fractionalNearFrameSubtreeG2R0429LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0429Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0429LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
