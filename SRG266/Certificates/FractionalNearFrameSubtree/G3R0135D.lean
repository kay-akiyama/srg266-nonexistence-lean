import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0135`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0135Mask : ℕ := 6839774498885130

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0135Witness : Array ℤ :=
  #[-65, -383, 418, 506, 365, -80, 351, 44, -541, -309, -151, 221, 1410,
  -468, 26, -168, -236, 150, -111, 10, 406, 673, 66, -749, 438, 274, -179,
  733, 218, 279, 426, -381, -401, 392, 849, 927, -90, -221, 619, 360, 0,
  -109, -706, -40, 2, 559, 668, -858, -137, -313, -158, 229, 1329, 1196,
  147, -324, -1602, 756, 856, -865, 1077, -99, -275, 0, -717, 450, -1140,
  -220, 2, 69, 320, 538, -899, 334, 734, -1548, 795, 176, 331, 177, -140,
  -681, -772, 191, -623, -90, -318, -620, -4, -568, -635, 850, 151, 1232,
  544, 720, 699, -104, 62, -678, -131, -415, 540, 361, -420, 68, 1058, 867,
  1240, 1050, -803, -1157, -555, 484, -1162, -384, -850, 206, 0, 41, 1157,
  -198, -220, 158, 639, 158, -37, 190, -762, -1203, 385, 779, 1068, -808,
  33, 278, 383, -1261, 621, 1269, 832, 93, -393, 395, 1058, 823, 1563, 921,
  -414, 394, -309, 728, -585, -550, -671, -103, -654, -944, 790, -525, 537,
  -547, 1457, -1018, 198, -2208, -1056, -889]

theorem fractionalNearFrameSubtreeG3R0135_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0135Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0135Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0135Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0135_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0135LowerBoundTable : List ℤ :=
  [-184, 32, -1188, 1464, 1443, 914, 33, -646, 31, 100, 2323, 728, -1061,
  687, 873, -821, 899, 3409, 1461, 100, 968, 2828, 727, 1669, 3479]

def fractionalNearFrameSubtreeG3R0135LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0135Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0135LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
