import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0186`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0186Mask : ℕ := 1388178131624304

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0186Witness : Array ℤ :=
  #[252, -765, -93, -813, -245, 976, 1219, 1013, 295, 473, -723, -400, -683,
  578, -477, -279, 394, 323, 178, 726, 199, 276, -252, -219, -94, -354, 295,
  -556, -57, 544, -962, 352, 164, -88, 0, -935, 623, 389, -660, 311, 1065,
  89, 0, -392, -367, 284, -9, 46, -72, 348, 633, -1008, 248, -723, -201,
  581, 572, -293, 163, 939, 242, -20, -703, -717, -409, 460, 88, 108, 128,
  -985, -336, 126, -21, 262, 271, -310, -854, -147, 522, 165, 527, -459,
  -686, 143, -198, -13, 116, 505, 338, 851, -292, -26, 684, 516, 432, -436,
  110, -312, -358, 235, -461, -930, 213, 361, -65, 589, -631, -1348, 249,
  1226, 240, -932, 46, -656, -189, -69, -974, -376, -87, 549, 1311, 166,
  -366, -898, -362, -547, 690, -63, -472, 109, -396, -338, -115, 431, 544,
  850, 793, 202, 1261, -499, -27, 874, 260, 182, -339, -115, 219, -800, 878,
  -290, -134, 133, -524, 83, 633, 206, -92, 725, 425, 210, -25, 946, -674,
  0, 249, 743, 805, 430]

theorem fractionalNearFrameSubtreeG2R0186_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0186Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0186Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0186Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0186_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0186LowerBoundTable : List ℤ :=
  [-262, 1559, 969, -711, 418, 32, 1034, -104, 119, 190, 1895, 2808, -1818,
  1676, 679, 1859, 959, 100, -2433, 2039, 2139, 251, -317, 1178, 1430]

def fractionalNearFrameSubtreeG2R0186LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0186Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0186LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
