import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0400`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0400Mask : ℕ := 5740389831779106

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0400Witness : Array ℤ :=
  #[0, 568, -3, 524, -380, 474, 328, 109, -351, 667, -434, -1006, 1173,
  -130, -41, 200, 623, -138, -357, -13, -621, 510, 213, 235, -95, 561, 55,
  18, -402, 281, 427, -76, 365, -82, -422, -765, 209, -114, -178, -207, 401,
  -744, -503, -163, 200, -124, 598, 2, -39, -91, -216, 3, -321, -672, -382,
  232, 674, -44, -356, 226, -863, 772, 79, -174, 319, -526, -385, 576,
  -1236, 1111, -1081, 7, 39, 310, -109, 123, -253, 388, -40, -234, -664,
  -372, 918, 595, 751, -226, 766, -452, 116, 331, 425, 697, 241, -455, 185,
  374, -145, 1394, 132, -346, -130, 188, -233, 17, -657, -217, 452, 92, 932,
  448, 281, 222, 413, 860, -1002, -1760, 455, -1655, -623, -1243, -193,
  -115, 281, 137, 0, 1464, -51, -301, -430, -442, -37, 238, 563, 479, 496,
  -99, 243, 223, -770, 600, 1456, -692, -543, 156, 658, -866, -282, 10, 203,
  -291, 166, 283, 616, 473, 796, -1254, 221, 317, 74, -280, -503, 2, 98,
  720, -811, -474, 139, 579]

theorem fractionalNearFrameSubtreeG2R0400_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0400Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0400Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0400Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0400_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0400LowerBoundTable : List ℤ :=
  [-354, 33, -113, 1970, -602, -476, 376, 32, 32, -111, 1376, 3771, -2877,
  -465, 1334, 327, 1867, 974, 97, 1162, 3040, 101, -1686, 300, 1430]

def fractionalNearFrameSubtreeG2R0400LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0400Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0400LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
