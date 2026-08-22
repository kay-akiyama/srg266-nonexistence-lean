import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0064`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0064Mask : ℕ := 815595511139092

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0064Witness : Array ℤ :=
  #[614, 323, 317, 626, 766, -510, -820, -611, 686, -664, -15, 228, -32,
  -237, 248, 85, -360, 30, -245, 148, -77, -173, 800, -79, -414, 319, -155,
  839, 660, 105, 417, 305, -223, -382, 644, -35, -868, -547, 377, 252, 473,
  -140, 732, -809, 417, -44, 484, -673, 12, 1052, -421, 768, 425, 110, 626,
  -545, -63, -129, -665, 483, -364, 7, 159, -529, 338, -322, -426, 426, 258,
  559, -242, 100, 148, -1154, 804, -279, 575, -673, 115, 67, 58, 432, 465,
  790, -44, 228, 459, -201, -667, 255, -434, 663, 307, -388, 9, -150, -724,
  -271, -372, -127, 480, 45, 340, -218, 485, 381, 635, 735, -607, 123, -879,
  -406, -1129, 304, -1023, 816, -6, 260, -753, -90, 102, 651, -950, 293,
  156, 386, -43, -187, -126, -788, -398, -471, 1034, 394, 761, -103, 462,
  1371, -189, -775, -161, -884, -863, -431, -378, -272, 460, -583, 638,
  -471, 280, -261, 36, 200, 570, -619, 543, 458, -532, -2, -1124, -365, 507,
  67, 55, 269, 621, 909]

theorem fractionalNearFrameSubtreeG1R0064_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0064Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0064Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0064Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0064_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0064LowerBoundTable : List ℤ :=
  [-354, -149, 1163, 32, 196, 32, -108, -230, 785, 100, 151, -743, 680, 98,
  1918, 157, 3496, 2014, -1027, -210, 1509, -930, 1116, 2484, -273]

def fractionalNearFrameSubtreeG1R0064LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0064Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0064LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
