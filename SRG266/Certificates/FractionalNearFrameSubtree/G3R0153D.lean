import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0153`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0153Mask : ℕ := 6850405981882584

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0153Witness : Array ℤ :=
  #[1114, -281, -374, 960, 582, 433, 763, -317, -231, -228, 558, -57, -541,
  -566, 365, -845, -943, -35, 476, 674, -657, 659, 289, -184, 597, -405,
  744, 47, 680, 592, 406, 1179, 327, -134, 386, -1252, -19, -21, -77, -75,
  -859, -144, -475, 381, -794, -645, -182, 1258, 1057, -223, 977, 111, 1112,
  841, 105, 202, 561, -616, 466, 543, -152, 56, 762, 562, 946, 290, 544,
  -626, -693, -32, 416, 56, 171, 456, 543, -1077, -182, 329, 1086, -859,
  588, 184, -654, -1116, 252, 150, 853, -193, 3, -317, -72, 280, -12, 55,
  308, -813, 258, -887, 65, 691, 680, -1004, 345, 57, 23, 13, 1488, -683,
  -94, 1108, -562, 598, 740, 217, -99, 806, 458, -475, 1352, 200, -1112,
  -1036, 1107, 752, 1068, -145, 1309, 172, 387, -358, 546, 45, 484, -578,
  244, 862, 1106, -107, 336, -377, -96, 1276, 361, -150, 118, -532, 509,
  1162, 617, 299, -354, 467, 511, 355, -287, -171, -6, -388, 1194, 579, 386,
  0, -875, 38, -879, 0, 513, 884]

theorem fractionalNearFrameSubtreeG3R0153_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0153Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0153Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0153Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0153_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0153LowerBoundTable : List ℤ :=
  [1179, 2394, 2006, 1623, 433, 3026, 1173, 1051, 1937, 5662, 3057, 1388,
  3335, -515, 3688, 946, 1454, 1300, 3025, 15, 627, 2135, -1524, 6601, 4563]

def fractionalNearFrameSubtreeG3R0153LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0153Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0153LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
