import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0004`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0004Mask : ℕ := 265924663775363

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0004Witness : Array ℤ :=
  #[219, -706, -640, -1791, -1262, -125, 409, 273, -1193, -319, -1134, -240,
  1166, 1427, 1345, 82, 998, 1450, 349, -1283, 60, -646, 702, 157, -105,
  -460, -22, -315, -485, 632, 72, 766, 0, -1298, -4, -962, -931, -239, 139,
  192, 170, 356, 600, 223, 28, -136, 288, 405, -179, -29, 293, 442, -99,
  -156, -1154, -619, 232, 339, -116, -1002, 668, 127, -47, 8, -181, 91, 150,
  1259, 1036, -439, -683, 486, 392, -283, 113, 510, 1217, -592, -34, -93,
  -39, 331, 372, 258, 150, 117, 606, 269, 282, 440, 886, -150, 876, 378,
  318, 181, 172, 709, -254, -573, 906, 255, 374, -151, -418, 79, 274, -310,
  -331, -599, -1084, -233, -42, -131, -214, -554, 380, 582, 656, 396, 21,
  -658, -841, -238, -54, 123, -507, -83, -295, -822, -156, 761, -11, -67,
  215, 41, -146, 243, 569, -381, 311, 207, -634, -215, -547, -377, 197,
  -109, -29, -399, 237, 453, -3, 378, -511, -136, 100, -120, 266, 625, 119,
  -1352, -239, -577, 51, 1300, 290, 470]

theorem fractionalNearFrameSubtreeG3R0004_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0004Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0004Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0004Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0004_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0004LowerBoundTable : List ℤ :=
  [-767, 31, 473, 61, -862, 32, 533, 997, -170, -618, -899, -927, 230, 3411,
  921, 100, 1815, -37, 1556, 1830, -1893, -1504, 976, 3645, 466]

def fractionalNearFrameSubtreeG3R0004LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0004Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0004LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
