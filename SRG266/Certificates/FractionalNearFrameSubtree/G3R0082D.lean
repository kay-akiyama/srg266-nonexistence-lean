import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0082`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0082Mask : ℕ := 2372045613505553

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0082Witness : Array ℤ :=
  #[0, -392, -828, -746, -790, -360, 1040, 1423, 354, 605, 642, 784, -825,
  348, -1885, 0, 1221, 167, 1140, -860, -746, -1031, -190, -1350, -65, 240,
  -1636, -927, 1119, 72, 3320, 2607, -351, -278, 325, -55, -904, 304, 37,
  1263, -1427, 449, -2684, 849, 175, -1305, -135, 1783, 127, 106, 779, -501,
  -681, 2094, -1518, 323, -525, -780, 1402, -230, 1970, -8, 478, -365, 1197,
  -594, 283, -832, -49, -43, 303, 100, 1120, -866, -274, 861, 598, 976,
  -1208, 188, 220, 1005, 288, -27, 599, 1255, -663, 1017, -1102, 1186, 1567,
  -350, 1415, 393, -336, 478, -49, 1030, 1108, 176, -28, 1098, 1036, -405,
  432, -122, 1079, 129, 1, 6, -346, -523, 219, -662, 646, 339, -518, 0,
  1160, 1465, -310, 358, -408, 14, -957, 632, -535, 854, -155, 347, -615,
  -322, 542, 2149, 341, -1673, 681, 1065, 423, -964, 858, 280, -1081, -581,
  1481, 0, -7, 529, 941, 498, 245, -317, -360, 837, -358, 963, -887, 116,
  385, 1808, 208, -219, 2631, -56, -880, -226, -1008, 60]

theorem fractionalNearFrameSubtreeG3R0082_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0082Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0082Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0082Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0082_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0082LowerBoundTable : List ℤ :=
  [1066, 2193, 605, 2980, 1778, 2348, 584, 465, 1379, 99, 2455, 99, 98,
  1599, -140, -722, 2457, 4705, 3424, 1996, 2208, 6341, 2356, 8152, 6646]

def fractionalNearFrameSubtreeG3R0082LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0082Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0082LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
