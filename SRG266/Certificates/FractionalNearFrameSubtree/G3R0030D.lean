import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0030`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0030Mask : ℕ := 954018842937994

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0030Witness : Array ℤ :=
  #[738, 587, 417, -845, 109, 284, -108, 288, 485, -886, -84, -287, 31, -11,
  503, -186, -5, -60, -251, -96, -539, 416, -17, -255, -111, -456, 104, 881,
  548, -446, -783, -655, -863, 874, 522, 302, 689, 391, 224, 372, 101, -539,
  -489, 78, -511, 767, 1269, -125, 142, 326, 246, 1277, -344, -571, -591,
  -270, -278, 201, 247, 1070, 633, 156, -486, 517, 958, -236, -257, 706,
  -422, 268, 339, -99, -274, -614, -12, 188, 104, 104, 0, 55, 438, 219, 228,
  516, 1466, 1232, 139, -506, -1, -429, -72, -505, 396, -74, 237, 841, 914,
  256, 120, -277, -134, 614, 436, 1168, 234, 375, 196, -267, 202, 32, -313,
  -277, -225, -645, -275, -181, -535, 196, 43, -347, -631, -510, -250, 0,
  573, 216, 124, -74, 750, 986, 616, 34, -135, -589, 847, -7, 166, -774,
  370, 100, 118, -33, -828, 131, 469, 420, 108, 275, 236, 452, 126, -176,
  81, 643, 63, 381, 499, -196, 321, -95, -705, 743, -66, -672, 458, -400,
  582, 1455]

theorem fractionalNearFrameSubtreeG3R0030_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0030Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0030Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0030Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0030_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0030LowerBoundTable : List ℤ :=
  [537, 927, 1751, 1811, -98, 563, 1632, 32, 2027, 1143, 127, -2008, 1386,
  2746, 3027, -771, 2128, -50, 730, 1173, 1638, 3331, 4097, 4240, 3349]

def fractionalNearFrameSubtreeG3R0030LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0030Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0030LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
