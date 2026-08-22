import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0195`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0195Mask : ℕ := 2338347466592771

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0195Witness : Array ℤ :=
  #[-164, -552, 87, -108, -704, 1356, 0, 216, 176, 314, 1352, 805, -1316, 0,
  -14, 401, -508, -583, 663, -361, 1373, 1557, 131, 3065, -1052, -929, -15,
  997, 1108, -1154, -2289, 443, -1055, -1196, 1817, 789, -43, -764, 148,
  730, -244, -387, 334, 1675, 301, -1416, 1130, 807, 816, 801, 72, -600,
  -635, -567, -739, 559, 237, 426, -808, 125, -125, -309, -63, 1019, 1076,
  175, 1202, 296, -1044, 510, 11, 19, 579, 128, 858, 647, 127, 103, 467,
  -301, -661, 333, -41, 308, -914, -270, 981, 547, 593, 638, 252, 1126, 142,
  547, 735, 1270, 939, -474, 1145, 241, 749, -37, -843, -446, -182, -962,
  890, -590, 363, -492, 619, -338, 912, 226, -1114, 1775, -830, -244, 426,
  -1190, 480, 797, 1194, -284, -26, 488, 681, -61, -1170, 383, -676, 549,
  260, 337, 772, 196, 304, 33, 120, 1323, -619, 708, -425, -244, 165, -18,
  -183, -465, -183, -121, 359, 819, -1645, 28, 637, 421, -1102, 309, -750,
  123, 13, 210, -1647, 697, 1003, 1236, 1311, -2043]

theorem fractionalNearFrameSubtreeG2R0195_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0195Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0195Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0195Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0195_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0195LowerBoundTable : List ℤ :=
  [1351, 1523, 2594, 916, 431, 3036, 2223, -3, 1276, 1467, 2577, 591, 316,
  1179, 3704, 3428, 5596, -818, 2581, 1399, 1702, 318, 1590, 4009, 100]

def fractionalNearFrameSubtreeG2R0195LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0195Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0195LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
