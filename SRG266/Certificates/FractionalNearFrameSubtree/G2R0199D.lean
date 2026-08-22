import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0199`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0199Mask : ℕ := 2339518753119249

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0199Witness : Array ℤ :=
  #[-1304, -641, -1274, -1558, -667, -245, -94, -92, 1018, 566, 1088, 558,
  574, 792, 476, 829, 86, 390, 548, 1329, 280, -113, -442, 37, -293, -773,
  -231, -1629, 815, 623, 92, 7, -161, 174, 315, -694, -264, -577, 0, -372,
  650, 823, 782, 517, -28, 538, 1111, -418, 260, -143, 1504, -287, 566,
  -1133, 76, 1163, 135, 386, 791, -51, 311, 227, -526, 535, 65, -269, -216,
  -134, 0, 178, -50, 262, 122, -350, 265, 700, 798, 208, 0, -1056, 738, 119,
  1006, -30, 930, 1365, 243, -515, -9, 185, -1278, -13, 685, 525, -362, 2,
  145, -1022, -503, -212, -1145, -1658, 904, 71, 1469, 819, 790, 814, 166,
  1192, 147, -227, -303, -717, 247, 276, -223, 71, 0, 418, 71, -3, -156,
  435, -61, 294, 120, 80, 729, -1107, 128, -445, 342, -513, 498, -488, 739,
  430, -822, -136, -356, 268, 72, -723, -591, -481, -766, 591, 569, 331,
  353, 297, -635, 297, -626, 247, 793, 288, 506, -195, -376, 561, -263, 298,
  1107, -457, 288, 277]

theorem fractionalNearFrameSubtreeG2R0199_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0199Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0199Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0199Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0199_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0199LowerBoundTable : List ℤ :=
  [666, 394, 3274, 31, 31, 32, 3389, 32, 2006, 1700, 769, 1669, 101, 4100,
  1407, 1121, 2568, -2379, -3009, 101, 2604, 3568, 101, 438, 1344]

def fractionalNearFrameSubtreeG2R0199LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0199Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0199LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
