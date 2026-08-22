import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0029`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0029Mask : ℕ := 830721454194904

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0029Witness : Array ℤ :=
  #[734, -992, 819, 47, -372, 113, -220, -92, -822, 846, -442, 454, 405,
  670, 845, -219, 277, 478, 576, 686, 236, -330, -271, -182, -123, 15, -259,
  347, -155, 1115, -1112, 100, 874, -77, 403, 9, -208, 0, -406, -806, -532,
  -1362, 698, -705, -1135, 532, -15, 141, 1864, 662, -938, -1177, 278, 699,
  18, 325, 729, 272, -1539, -207, -676, -85, -6, 228, 495, -221, 568, -678,
  924, -6, -154, 456, -524, 68, -552, 827, -1856, -789, 62, 407, 577, -346,
  929, -363, 28, 246, 350, 1914, 946, -775, -97, 460, 489, 82, -125, 338,
  372, 518, -1402, 272, -92, -662, 710, 144, 535, 420, 861, 774, -424, -234,
  -606, -1156, -418, 186, -145, -270, -278, -471, 191, 52, 44, 118, -242,
  -537, -750, 719, -31, -451, 631, 19, -1630, 77, 366, 235, 531, 59, 789,
  -310, 1213, -659, 1658, -578, 983, 1348, -1280, -442, 323, 960, -369,
  -158, -652, -476, 443, 397, 201, -184, 148, 0, -55, -7, -732, -201, -623,
  -313, 766, 148, 8, 20]

theorem fractionalNearFrameSubtreeG2R0029_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0029Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0029Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0029Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0029_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0029LowerBoundTable : List ℤ :=
  [-426, 32, -460, 923, -498, 1946, 2143, -442, -257, 176, 2333, 517, -973,
  859, 1653, 100, -4866, 3056, 4303, -2033, -76, 1442, -509, 1472, 1555]

def fractionalNearFrameSubtreeG2R0029LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0029Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0029LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
