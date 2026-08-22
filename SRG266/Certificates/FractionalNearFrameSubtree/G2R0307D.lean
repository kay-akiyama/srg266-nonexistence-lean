import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0307`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0307Mask : ℕ := 5387248084917784

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0307Witness : Array ℤ :=
  #[226, 402, 785, 474, 160, -230, -16, -499, -164, -487, 224, 168, -216,
  -435, 614, 909, 46, 55, 100, -497, 867, 687, 199, -561, 212, -890, -468,
  -297, 914, -468, -209, -556, -259, 699, 352, 116, -276, 241, 335, 84,
  -282, 760, 215, -143, -880, 484, 515, 296, 151, -213, 103, -220, -316,
  534, 102, -2689, 317, -20, -723, -316, 412, -1473, -564, 566, -118, -656,
  33, 380, -226, 663, 185, -230, 295, -264, 1045, 364, -634, -880, 262, 16,
  259, 8, 87, 10, 297, -1401, 46, -361, 797, 571, -50, -731, -263, 561, 269,
  821, -16, -52, 715, 201, 180, -152, 238, 3, 174, 312, 446, -638, -100, 63,
  106, 739, 1235, 417, 485, 825, 773, 664, 535, 1481, -1769, -331, 157,
  -870, -205, -47, 653, -443, 414, 231, -4, -748, -475, -52, -70, -7, -42,
  -504, -390, 434, -252, 440, 642, -231, -1129, -652, -577, 648, -396, -503,
  422, -178, 111, 789, 373, 353, 242, 134, 1233, -899, 66, -541, 254, -122,
  -604, -721, 605, -157]

theorem fractionalNearFrameSubtreeG2R0307_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0307Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0307Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0307Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0307_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0307LowerBoundTable : List ℤ :=
  [-368, 56, 665, 30, 1510, -1280, 32, 110, 33, 100, 100, -10, 1323, 101,
  1542, -238, -551, 994, 1245, 386, 1044, 2491, 934, 2362, 442]

def fractionalNearFrameSubtreeG2R0307LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0307Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0307LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
