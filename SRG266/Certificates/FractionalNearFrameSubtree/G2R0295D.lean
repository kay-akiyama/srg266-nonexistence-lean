import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0295`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0295Mask : ℕ := 5387148380968020

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0295Witness : Array ℤ :=
  #[-506, 1065, -225, 0, -225, -1578, -1358, -820, -940, 192, 669, 156,
  1525, 716, 1159, -402, -2104, -1055, 740, 1025, 961, 747, -51, 1287, 404,
  1136, -1623, -1613, 572, 882, -866, -1111, -1025, -1121, -1724, -1290,
  1363, 535, 2020, -1302, -1112, -1029, 2695, 1169, 393, 174, -339, -829,
  -778, -414, 537, 841, 190, -1454, -1051, 0, 756, 913, 579, -706, 1, -441,
  -1190, -1251, -404, -30, 1458, 457, 1147, 645, -472, -336, -606, -147,
  -1060, 1350, 372, -474, 714, -137, -288, 611, -133, -126, 1402, 1143, 578,
  -568, 460, -282, -627, 31, -943, 1020, 1175, -576, 765, -363, 533, 742,
  -72, -144, -370, 1114, 938, -1675, -633, -1231, 204, 147, -881, -590, 918,
  1617, -714, 83, -206, 174, 914, 1011, 337, -618, 428, -1075, -1021, -391,
  201, 729, 843, -1065, -130, -1049, -979, 1408, 1768, 1078, 1408, 1031,
  -533, -67, 1154, 1946, 675, 798, 972, -857, 388, -354, 1132, -102, -860,
  -599, 113, -1227, -753, -689, -335, -1236, -919, 689, -66, 591, 158, 444,
  -483, 26, -305, -1954]

theorem fractionalNearFrameSubtreeG2R0295_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0295Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0295Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0295Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0295_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0295LowerBoundTable : List ℤ :=
  [-572, -341, 32, 3006, 879, -984, 31, 31, -2030, -1600, 4123, 834, 101,
  -1349, -1105, -3632, 101, 3797, 4483, -173, 2086, -851, 3393, -1139, -207]

def fractionalNearFrameSubtreeG2R0295LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0295Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0295LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
