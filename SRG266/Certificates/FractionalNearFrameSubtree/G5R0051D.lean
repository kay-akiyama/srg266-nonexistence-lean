import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0051`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0051Mask : ℕ := 4908729704882435

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0051Witness : Array ℤ :=
  #[-114, 264, 209, -61, 214, -221, -91, 1442, 556, 145, 832, -362, -555,
  -988, 89, 292, -500, -167, 105, -602, -76, 100, 576, 150, 398, 577, 402,
  -767, -543, 665, 0, 285, -236, 286, 451, -753, -43, 590, -827, -166, 717,
  -415, 923, -766, -221, 98, -886, 117, 133, 1023, 167, -517, -280, -49,
  173, 432, 501, -761, 840, -394, 117, 277, 163, -389, 371, -1302, 67, 414,
  226, 586, -109, -405, 484, -156, -1069, 1356, 1301, -616, -483, 967, 217,
  831, 317, -366, -383, 482, -422, 31, 122, -672, -171, 101, -25, 709, 69,
  265, 837, 224, 257, 211, 190, 869, -47, -9, 1353, 0, 900, -905, -1259,
  -185, -207, 200, -206, -25, -449, -229, -907, 576, 187, -141, 1139, 356,
  -186, 156, 267, 238, 868, 253, 552, 869, -643, 109, 932, -282, -354, 103,
  -322, 52, 733, 534, -243, -1378, -115, -234, -323, 40, 92, -226, -646,
  -329, 197, -626, 659, 1147, 574, 906, 1128, 115, -279, 966, 1640, 166,
  -90, 681, -90, 272, 253, -957]

theorem fractionalNearFrameSubtreeG5R0051_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0051Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0051Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0051Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0051_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0051LowerBoundTable : List ℤ :=
  [854, 1424, 883, 72, 1273, 135, 2178, 1418, -141, 1273, 2612, 1686, -765,
  993, 2851, 2736, 830, 719, 963, 1618, 100, 6473, 2228, 98, -539]

def fractionalNearFrameSubtreeG5R0051LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0051Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0051LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
