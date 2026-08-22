import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0626`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0626Mask : ℕ := 11275160931375649

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0626Witness : Array ℤ :=
  #[0, -405, 468, 676, 356, -55, 0, -634, -540, 849, 1052, 1294, -1269, -5,
  -908, 902, 426, 1679, 42, 975, -285, 403, -35, 90, -779, 518, 522, 312,
  -269, -282, -69, 972, -416, -1007, -202, 502, 620, -880, -667, -341,
  -1240, -89, 773, 1446, 588, 926, 1006, 0, 473, 109, -1029, -977, 297, 291,
  -545, -465, 255, -77, 92, -381, 522, -1085, 812, 1538, -393, -859, 1176,
  -1141, 716, -371, -403, 58, 43, -53, -1262, 457, 619, 155, -7, 757, -863,
  767, -288, -764, 159, 128, -800, 142, -1105, -232, 313, -750, -998, -195,
  71, -471, -345, 348, -243, 98, -305, -840, 492, -547, -187, -1208, 80,
  161, -1119, 599, 60, -135, -248, 203, 305, 468, -211, 983, 394, 685, 821,
  225, -35, -445, -762, 1045, 1700, 430, 82, 605, 701, 728, -206, 738, 292,
  273, 636, -192, -692, -99, -317, 254, 179, -184, -37, 155, -475, 226,
  -134, -511, -1074, -342, 609, 726, 758, -302, 0, -1070, -532, -548, 182,
  -818, -443, -428, 511, -1381, -1619, -530]

theorem fractionalNearFrameSubtreeG2R0626_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0626Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0626Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0626Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0626_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0626LowerBoundTable : List ℤ :=
  [-867, -1115, -2816, -748, 1281, -760, 32, 32, 3463, -1255, 797, 2676,
  1501, -1911, 2107, -1018, 1937, -963, -1579, 2260, 1420, 758, 3237, -1706,
  -2272]

def fractionalNearFrameSubtreeG2R0626LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0626Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0626LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
