import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0023`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0023Mask : ℕ := 1084721144234322

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0023Witness : Array ℤ :=
  #[205, -176, 461, -894, 28, 234, -562, -633, -948, -619, 26, 277, -231,
  485, 80, 1134, 1290, -3, 108, -114, 173, 520, -13, -326, -575, -651, 413,
  291, -309, -785, -37, 280, 319, 9, 332, -227, 192, 183, 258, 17, 1130,
  -1121, -606, 90, -525, -166, -558, -77, 241, 210, 595, 103, 152, 1419,
  -600, 9, 956, 374, -354, 642, -371, -107, 232, -252, -135, 452, -268, 288,
  -87, 13, 55, -122, 422, -370, -647, -87, -244, 196, 34, -789, -274, 825,
  715, 830, 229, 153, 165, -526, 18, -296, 958, 614, 291, 388, -51, 228,
  -284, -326, 40, -526, -350, 278, -439, -129, 82, 426, 34, 35, 631, -696,
  -163, -135, -368, -149, 191, 944, 331, 0, 129, 65, 161, -1002, -476, 21,
  28, 229, -286, -634, -513, -40, 483, 701, -466, 230, 375, 333, 332, 303,
  -185, -656, 541, -486, 29, -136, 128, 390, -1132, 412, 694, -959, 4, -922,
  1, 187, 71, -6, 293, 169, 615, 362, 0, -1126, -148, -128, 333, 714, -514,
  589]

theorem fractionalNearFrameSubtreeG5R0023_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0023Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0023Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0023Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0023_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0023LowerBoundTable : List ℤ :=
  [-323, 164, 1064, 34, 690, 794, -388, -135, 32, -89, -658, 100, 96, 1422,
  1469, 2121, -1898, 1687, -2210, -615, 895, 554, 1152, 1261, 890]

def fractionalNearFrameSubtreeG5R0023LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0023Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0023LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
