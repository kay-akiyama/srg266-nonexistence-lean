import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0141`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0141Mask : ℕ := 6855030144218129

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0141Witness : Array ℤ :=
  #[-156, -338, 364, 236, -71, -25, -92, -165, 298, -538, -150, 262, 208,
  645, -27, -218, -55, 154, 385, 36, 136, -150, 257, 127, 484, -231, -63,
  -552, -290, 131, -280, -486, -45, 328, -193, -522, 121, 0, 482, 157, 567,
  102, 189, 146, 229, 85, -470, 794, 77, -82, 537, -73, -288, -437, 508,
  -122, 27, 414, 200, -198, 580, 324, -227, -414, 0, -752, -29, 344, -422,
  448, -321, -69, 385, 201, 512, -409, 46, -147, 35, -450, 325, -38, 30,
  -63, -463, 384, -306, -383, 25, 50, 235, 437, 36, 20, 450, -340, -50, 103,
  111, 416, 402, 159, 81, 493, 23, -189, 208, -297, -363, -142, 359, 504,
  638, 944, 181, -279, -373, 497, 131, 345, -526, -1309, -195, -351, 324,
  124, 380, 143, -386, -183, -709, -345, -250, 50, -415, 56, -527, 397,
  -265, 47, -178, 461, 1422, 527, 483, 132, 357, -50, 361, 526, -45, -296,
  -78, 98, -312, 190, -141, -377, 611, -304, -942, 400, -825, 5, 263, 288,
  -51, -598]

theorem fractionalNearFrameSubtreeG5R0141_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0141Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0141Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0141Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0141_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0141LowerBoundTable : List ℤ :=
  [-97, 31, -406, 432, 1473, 32, 31, 164, 284, 863, -1287, 182, 43, 1428,
  1635, 631, 99, 100, 2126, 2168, 569, 999, -522, 14, 543]

def fractionalNearFrameSubtreeG5R0141LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0141Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0141LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
