import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0160`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0160Mask : ℕ := 1379521495212706

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0160Witness : Array ℤ :=
  #[553, -246, 793, 573, -1088, 535, 258, 474, -1426, 296, -1324, 1361, 591,
  701, -400, 1596, -74, 71, 239, 276, -145, -392, 112, 509, 143, 1216, 91,
  -623, -646, 151, -734, -1068, -679, -42, 733, 577, 656, -256, 65, 83, 187,
  -167, 443, -1197, 105, 260, 651, -194, -83, 116, 381, 10, 267, -276, 229,
  -467, 279, 563, 281, -424, -36, 0, 742, -73, -425, -140, 400, 1097, 62,
  -8, -227, -46, -506, -655, -353, -50, -1405, 441, 486, 416, 234, 366,
  -212, -472, 359, -25, 499, 761, 331, -104, 356, 957, 348, 387, 889, 230,
  938, 4, 88, 169, 197, 985, -5, 156, -329, 192, 482, 379, -78, 1390, -209,
  310, -554, 425, -64, 207, 152, -65, -403, -531, 606, 530, -299, 282, -51,
  -393, 463, -130, 829, -83, 138, -108, 228, 127, -41, -346, -832, -383,
  -619, -466, 898, -6, -69, -178, -251, -132, -531, -474, -709, 52, -435,
  1251, 132, 597, 641, -865, 376, 554, 315, -189, -95, -308, -350, 495,
  -806, -62, -23, 664]

theorem fractionalNearFrameSubtreeG2R0160_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0160Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0160Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0160Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0160_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0160LowerBoundTable : List ℤ :=
  [387, -517, 411, 1739, 32, 2948, -696, 1175, 1151, 1689, 1352, 98, 758,
  -563, -1721, 486, 1373, 1427, 3513, 4809, -317, 2511, 1630, 553, 3709]

def fractionalNearFrameSubtreeG2R0160LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0160Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0160LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
