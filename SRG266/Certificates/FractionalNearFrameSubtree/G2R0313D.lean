import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0313`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0313Mask : ℕ := 5388967023863308

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0313Witness : Array ℤ :=
  #[-93, -285, 0, 507, 611, 988, 795, 1363, 2286, 467, 161, 492, -1214, -26,
  838, -1161, -314, 1025, 779, 785, -151, 1288, -65, 680, -557, -236, 852,
  48, 814, -793, -314, -226, 415, 470, 376, 1097, -691, 190, -168, -56, 445,
  1245, -115, -1454, 537, 627, 697, 745, -109, 1838, -258, 397, -224, 97,
  -94, 624, -403, 105, -659, 926, 1109, 1228, -854, -765, 340, 29, 397,
  -416, 1406, 419, -114, 972, 1596, -566, -258, -3, -60, -681, 1546, 249,
  282, 752, 448, -440, 180, 2138, 1375, -452, -366, 415, -188, 635, 362,
  715, -1363, -692, 246, 581, -912, -961, 53, 510, -331, 565, -373, -185,
  789, -858, 736, 402, -157, 251, -541, 34, -655, 78, 385, 1498, 907, 109,
  -132, 913, 601, -1453, 386, 1823, 372, -281, 479, 516, -101, 394, -1094,
  0, -680, 1405, -51, 631, 1094, 542, 168, 18, 653, 792, 432, 423, 791,
  -576, 725, 446, 362, 730, 316, -575, 938, -59, 18, -64, -209, 193, -106,
  1028, 599, 161, -634, 1503, -537, 217]

theorem fractionalNearFrameSubtreeG2R0313_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0313Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0313Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0313Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0313_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0313LowerBoundTable : List ℤ :=
  [2332, 3575, 1000, 2645, 1582, 1667, 4652, 3890, 2512, 219, 3015, 4564,
  5670, 2734, 1744, -1401, 1131, 1441, 6410, 6419, 6421, 4368, 100, 5134,
  4847]

def fractionalNearFrameSubtreeG2R0313LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0313Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0313LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
