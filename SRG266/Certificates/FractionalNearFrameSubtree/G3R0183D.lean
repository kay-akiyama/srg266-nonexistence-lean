import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0183`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0183Mask : ℕ := 6866159556037410

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0183Witness : Array ℤ :=
  #[-640, -349, 317, -259, -1007, -152, -274, -373, -321, -657, -441, 542,
  1389, 863, 12, 466, -864, -178, 102, 668, -687, -56, 41, 324, -37, -202,
  -179, 10, 243, 288, -729, -321, -926, -407, -324, 246, 308, 338, 9, 1153,
  195, 413, 663, 735, -503, -605, 615, 286, -355, -289, -18, 1032, 228, 189,
  -633, -493, -823, -119, -182, -74, 72, 66, 743, -164, -288, -207, 632,
  350, -1118, 0, -89, -1006, 175, -589, -863, 427, -333, -95, -973, -372,
  -210, 338, 499, -155, -263, 808, 106, 205, 865, 198, 91, -25, 738, 263,
  133, 658, 475, 639, -143, -556, 39, 471, -60, -118, 615, 588, -315, 324,
  -322, 507, 846, 264, 638, 149, 74, -540, -147, 286, 197, -132, 192, -379,
  -308, 100, -30, -67, 116, -300, 312, 289, 430, -680, 713, -481, 340, 1106,
  -135, -725, 23, -383, 602, 252, 0, -98, -659, 4, 750, 715, 279, 500, -464,
  -569, 639, -72, -1038, -36, 635, -777, -1396, 496, -884, -54, -300, 154,
  452, 355, -15, -933]

theorem fractionalNearFrameSubtreeG3R0183_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0183Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0183Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0183Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0183_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0183LowerBoundTable : List ℤ :=
  [-417, -214, 32, 31, 619, 552, -796, 93, -199, 100, 2581, 1509, 804, 2399,
  -2182, 100, 979, 559, -912, 1075, -339, 1003, 101, -624, 102]

def fractionalNearFrameSubtreeG3R0183LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0183Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0183LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
