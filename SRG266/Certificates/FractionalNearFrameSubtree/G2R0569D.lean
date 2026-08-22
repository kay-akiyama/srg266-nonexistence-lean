import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0569`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0569Mask : ℕ := 6846493173421202

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0569Witness : Array ℤ :=
  #[342, 916, 779, 2328, 131, 422, 558, -1322, -564, -827, -505, -729,
  -1374, 117, 549, -109, 200, 528, -395, 907, -279, 1481, -73, -865, -75,
  -830, -791, 86, 62, 639, 297, 369, -1265, -374, 30, 111, -117, 1254, 602,
  749, 971, 350, 313, -93, 302, -358, -254, -629, 105, -673, 846, 614, -7,
  -690, 192, 1463, -690, 725, 148, -2, -677, 410, 1509, -236, 197, -1464,
  500, 1197, 1046, -407, 547, 174, 1407, 272, 0, 715, -300, -409, 372, 247,
  -372, -2180, 1996, 245, 263, 0, 1047, 402, 975, -299, -208, 212, 531,
  -428, -190, -297, 1737, 906, 870, 572, 302, 630, 455, 556, 627, 1395, 995,
  1782, -249, -192, -814, 84, -1734, -139, -1155, -1244, 120, -463, -384,
  -936, 948, 391, 1413, -179, 426, -309, -91, 229, 114, 702, 519, -86, 408,
  -1083, -600, 611, 640, 4, 1036, 799, 288, 676, 645, 0, 1082, -111, 234,
  -441, 71, -188, -706, 248, 1797, 18, 2, 1730, -521, 385, -545, 50, 865,
  710, 76, -575, -1883, -385, 364, 525]

theorem fractionalNearFrameSubtreeG2R0569_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0569Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0569Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0569Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0569_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0569LowerBoundTable : List ℤ :=
  [1479, 1531, 2223, 3929, 2421, -119, 265, 2592, 670, 1441, -376, 3418, 99,
  -771, 2305, 5539, 1967, 3432, 2802, 7902, 3820, -326, 3975, -1538, 3139]

def fractionalNearFrameSubtreeG2R0569LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0569Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0569LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
