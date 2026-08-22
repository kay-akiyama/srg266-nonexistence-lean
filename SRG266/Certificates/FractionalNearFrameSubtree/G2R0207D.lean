import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0207`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0207Mask : ℕ := 2355819226837537

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0207Witness : Array ℤ :=
  #[-424, -1189, 52, 406, -739, -35, 1933, 985, 2335, 2259, 2916, 2636,
  -1670, -2141, -828, -1516, -1191, -1877, 436, 152, -704, -217, -452,
  -1873, 236, -279, -686, -118, 1203, 712, 403, 2669, 887, 1694, 375, 560,
  254, 106, -927, -1051, 797, 284, 482, -87, -150, 477, -215, 888, 1011,
  -650, -774, 1710, 763, -814, -588, 54, -1042, -1119, 83, 638, 246, 472,
  1541, 718, 1897, -771, 95, 531, 1206, -1242, -531, -354, -331, 1701, 647,
  94, -314, -413, 922, 582, -733, -374, -630, -84, 394, -793, -303, -147,
  -39, -515, -659, -265, 567, 244, 287, -368, 577, -358, -443, -718, 237,
  -922, -114, -577, 184, 306, 137, -553, -522, 423, 1088, -18, 0, 177, 23,
  1231, -550, 181, -17, 846, -77, -208, -43, 0, -491, -737, 373, -221, -221,
  0, 1, -869, 985, 697, 237, -262, -244, -1100, -867, 1215, -642, -37, -665,
  105, 612, -494, 175, 11, -307, 186, -540, -248, 291, -517, -275, -385,
  302, -157, 111, -437, -510, 157, 1041, 825, 356, 999, 1038, -1803]

theorem fractionalNearFrameSubtreeG2R0207_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0207Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0207Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0207Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0207_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0207LowerBoundTable : List ℤ :=
  [19, 26, 766, -1590, 31, 1770, -1001, 33, 2562, 1451, -2348, 1139, 1971,
  1874, 450, 3577, 2605, -2573, 2652, -1026, 2377, 204, 5540, 2163, -460]

def fractionalNearFrameSubtreeG2R0207LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0207Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0207LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
