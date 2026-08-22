import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0009`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0009Mask : ℕ := 275545375551633

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0009Witness : Array ℤ :=
  #[0, 452, -155, -209, -164, 663, -246, 319, -300, -235, 674, -41, 248, 52,
  -338, -718, 0, -189, -56, 81, -349, -665, -129, 217, 322, 734, -266, -185,
  -283, 679, 199, -276, -55, -45, -120, 103, 238, 225, 265, -307, -1116,
  315, -606, 171, -592, 495, 330, -134, 115, -161, -205, -113, -336, -309,
  739, 123, 101, 199, 96, 0, 542, -1, -213, -381, -516, -764, 106, 509, 187,
  -535, 309, 26, 34, -910, 282, 662, 84, 539, -602, 318, -813, -464, 118,
  732, 258, 308, 613, -54, -936, -102, -263, 63, -629, -410, 43, 409, 526,
  162, 397, -122, -745, -561, 106, -299, 711, -548, -569, -46, 144, 847,
  -107, -530, -1044, -275, -671, -98, 773, 211, -19, -13, -151, -146, -228,
  844, -166, 1849, -475, -1016, -129, -348, -59, 372, 412, 289, 821, 329,
  -241, 734, 313, 477, 389, -500, 201, -60, -324, 202, 255, 196, -761, -641,
  469, -323, 1032, -668, -206, -1117, 218, -613, -825, -1365, 66, 449, 243,
  261, 352, 903, 703, 273]

theorem fractionalNearFrameSubtreeG3R0009_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0009Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0009Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0009Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0009_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0009LowerBoundTable : List ℤ :=
  [-670, 138, 123, -1245, 32, 32, -732, 32, -236, 254, -217, 740, 667, 2267,
  -885, 2777, -661, -2067, 630, 1199, 101, 560, -561, 449, -160]

def fractionalNearFrameSubtreeG3R0009LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0009Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0009LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
