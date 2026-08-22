import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0601`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0601Mask : ℕ := 6880963787997784

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0601Witness : Array ℤ :=
  #[525, 147, 1439, -475, 485, 145, 650, -35, -326, -1039, -241, 499, -1321,
  -715, -118, 82, -473, -23, 533, -351, -8, 194, -522, -606, 462, 147, 192,
  2, -213, 99, 282, 1447, -275, 1063, -255, -1225, -250, -218, 379, 476,
  -241, -332, -408, -311, -89, 660, -725, 0, 140, 1005, -791, -172, -332,
  1047, 1220, 652, 428, -1335, 469, -240, 0, 871, -459, 91, -415, 805, 583,
  -49, -277, 117, -509, 89, 186, 258, 644, -162, 434, -256, -640, -816, 457,
  477, 939, 551, -932, 378, -364, 263, -21, -418, 268, -264, 188, -557,
  -444, -541, 114, -329, 471, 222, -401, -850, -99, -59, 346, -313, 93,
  -177, -424, -602, 107, 348, 651, 867, 168, 802, 1221, -337, -1488, -376,
  131, -69, 138, -73, 317, -155, -69, -1, 290, 335, -22, -286, 428, 708,
  701, -165, 796, -942, 81, 306, 770, 387, 486, 130, -317, 612, 402, 557,
  38, -669, 138, 177, 834, 747, -1183, -501, 487, 0, 307, -586, -68, 629,
  -740, -124, 106, 287, 965, 775]

theorem fractionalNearFrameSubtreeG2R0601_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0601Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0601Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0601Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0601_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0601LowerBoundTable : List ℤ :=
  [-53, 1049, 1601, 463, 32, 1575, -99, 1204, -1248, 1882, 1898, 1913, 99,
  888, 1640, 785, 1690, -1479, 123, 1215, 918, -1729, 1642, -416, 4107]

def fractionalNearFrameSubtreeG2R0601LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0601Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0601LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
