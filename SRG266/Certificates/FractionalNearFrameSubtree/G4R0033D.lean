import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G4R0033`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0033Mask : ℕ := 5432466315250962

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0033Witness : Array ℤ :=
  #[513, 791, -250, -102, 1322, 849, 0, -102, -354, 99, -442, 163, -790, 96,
  -518, -695, 86, 455, -171, -321, 617, 289, 224, -74, 388, 201, -977, -440,
  -149, -146, 455, 327, 5, -274, -51, -525, 518, 697, -398, -252, -356,
  -911, -773, -1214, -709, -5, 272, 259, 905, 1193, 1148, 950, 647, -1041,
  346, 211, 0, -85, -261, -163, 89, -893, -350, -48, 226, -287, -348, 389,
  164, 212, -476, 325, 278, 601, 741, -511, 510, -793, -680, -125, -494,
  -208, 1149, -14, 338, 470, -46, -469, -258, -418, -556, -421, -723, 333,
  126, 654, -989, 171, 99, -543, -279, 139, 254, 305, 54, -201, 49, -337,
  203, 466, -375, 38, 0, 323, 543, -307, 0, 19, -14, 453, -236, 164, -168,
  -9, 830, -36, -342, -313, -378, -345, -64, 589, -39, -867, -168, -957,
  158, -294, -702, 430, 698, 820, 679, -224, -617, -64, -783, -816, -1211,
  613, 666, -559, 309, -295, -297, 358, 1501, 373, 249, 302, -225, 134, 652,
  -204, 599, 656, 448, 504]

theorem fractionalNearFrameSubtreeG4R0033_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0033Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0033Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0033Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0033_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0033LowerBoundTable : List ℤ :=
  [-398, 977, 32, 216, 405, 787, -170, -249, -835, -851, 102, 100, 34, 101,
  -325, -1757, 1882, 1929, -68, -912, 1982, -981, 700, 1870, 1126]

def fractionalNearFrameSubtreeG4R0033LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0033Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0033LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
