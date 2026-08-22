import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0377`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0377Mask : ℕ := 5738022404039050

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0377Witness : Array ℤ :=
  #[59, 870, 420, -23, -81, 762, 866, 1120, 628, 129, 505, -186, -1200,
  -645, -895, -1214, -455, -205, -463, -238, -331, -22, 149, -679, 282,
  -146, 634, 641, 429, 250, 449, -171, -506, 213, -204, 532, 289, 338, 318,
  -461, 317, 24, 236, 466, 637, 607, -328, 401, 125, -689, -470, 68, -282,
  -650, -39, -368, -827, 1256, 391, -672, 708, -871, 745, -948, 420, -394,
  -390, 265, -16, -551, -529, -277, 969, 424, 709, -499, 883, -170, 326,
  -471, -12, -517, 239, 60, 329, 78, -34, -158, 281, 550, -344, -12, -49,
  -52, 706, 23, 85, 318, -63, -196, 802, 821, 26, 422, -303, 242, -771, 498,
  -484, 552, 156, 187, -404, -169, 52, -98, -282, 330, 387, -1407, 58, -510,
  555, -305, -225, 448, -722, -326, 680, 620, -319, -434, 489, -682, 540,
  410, -919, 279, -52, 132, 692, 302, -121, 149, 293, -473, 544, 337, -518,
  -164, 334, -2, -218, 306, 330, 587, -608, -66, 110, 457, 66, 456, 228, 88,
  14, 668, 512, 417]

theorem fractionalNearFrameSubtreeG2R0377_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0377Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0377Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0377Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0377_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0377LowerBoundTable : List ℤ :=
  [121, 805, 1075, 638, 156, 32, 1548, 33, 329, 1807, 2778, 177, 785, 100,
  2354, 888, 100, -66, 1089, -2191, 633, 1439, 101, 2751, 1161]

def fractionalNearFrameSubtreeG2R0377LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0377Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0377LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
