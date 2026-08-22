import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0102`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0102Mask : ℕ := 1275342926809603

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0102Witness : Array ℤ :=
  #[-231, -126, -504, -363, -698, 0, 41, -313, -260, -269, -2, -697, 561,
  672, 274, 455, 417, 148, 311, 248, 99, -41, -207, 357, -188, -109, -46, 0,
  -642, -23, 3, 31, 475, -738, -85, 207, -352, -273, 89, 184, 146, -329, 19,
  -482, 579, 145, 576, 0, -15, 683, -359, -123, -32, 281, -25, 140, 53, -90,
  428, 239, -1044, 248, -169, -171, -406, 201, 245, 33, -136, -273, -444,
  345, 117, 403, 54, 519, -28, -241, 142, 197, -98, 486, 6, -403, -266, 543,
  204, 581, -104, -271, 288, 18, -222, -247, 293, -59, 540, 301, 223, 362,
  327, 91, -290, 7, -190, 28, -304, -104, -167, 21, -190, -189, -477, -372,
  -134, -376, 2, -340, -282, 1452, -11, -360, 196, 243, 169, -178, -131,
  411, 191, -339, -30, 229, 369, -276, 39, 190, 156, -104, 168, -143, -289,
  95, 267, 183, 21, -311, -141, 497, 167, 211, -205, 532, -111, 988, -96,
  -374, -9, -347, -510, 125, -15, 56, 264, -180, 137, 151, 36, -294]

theorem fractionalNearFrameSubtreeG2R0102_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0102Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0102Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0102Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0102_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0102LowerBoundTable : List ℤ :=
  [-403, 605, 113, -370, -262, 33, 497, -497, 718, 3171, 202, 651, 175, 895,
  1094, 525, 1536, 298, -118, -316, -217, -475, 100, 100, 102]

def fractionalNearFrameSubtreeG2R0102LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0102Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0102LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
