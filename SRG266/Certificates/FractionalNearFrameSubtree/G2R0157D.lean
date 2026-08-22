import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0157`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0157Mask : ℕ := 1379248764732562

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0157Witness : Array ℤ :=
  #[529, 1495, 539, 525, 1587, 277, 0, 121, -1070, -1350, -1759, -301, 101,
  774, 357, 998, 781, 541, 101, 822, -932, 828, 394, 1068, 401, 458, -975,
  438, -755, 477, -110, 881, -866, -859, -633, 108, 541, 879, 1004, 510,
  168, 128, 284, 1599, 1236, 0, -723, 771, -433, 44, 8, 827, -336, -1359,
  -82, 285, 899, -728, 1493, 1739, -517, 261, 416, 62, 310, 370, -267, 1016,
  -270, 95, 141, -54, -105, 367, 187, -319, 1172, 116, 1259, 102, 485, -116,
  -262, -243, -462, 234, -648, -1592, -230, -388, -85, -31, -120, 652, 259,
  327, 640, 335, 177, 483, 156, 474, -119, 467, 88, -5, -16, 643, 107, 45,
  117, -535, 449, 356, -494, -1038, -101, -938, -369, 108, 126, 754, 440,
  -124, -1086, -391, -152, 386, 378, 216, -404, -501, -398, -268, -206, 522,
  -1919, 893, 198, 864, 395, -346, 189, -283, 161, 154, 0, 1269, 855, 447,
  1278, -35, 885, -506, 435, 785, 956, -790, 1375, 136, 409, -271, -345,
  -58, -879, 3, -714, 684]

theorem fractionalNearFrameSubtreeG2R0157_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0157Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0157Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0157Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0157_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0157LowerBoundTable : List ℤ :=
  [720, 1212, 911, 3124, 424, 690, 3490, 1189, 917, 1407, 2332, 63, 567, 99,
  5662, 900, -179, 2713, 2577, 3558, 2513, 4205, 99, 3068, 2191]

def fractionalNearFrameSubtreeG2R0157LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0157Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0157LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
