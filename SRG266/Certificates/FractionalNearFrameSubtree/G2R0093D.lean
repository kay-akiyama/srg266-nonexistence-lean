import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0093`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0093Mask : ℕ := 1239594942450697

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0093Witness : Array ℤ :=
  #[153, 1103, 806, -168, -77, -379, 840, 169, -191, -450, 0, 629, 133,
  -888, -221, -1070, -831, -796, 609, -580, -681, -753, -1114, 663, 186,
  -509, -561, -1283, 2085, 919, 1115, 1561, -71, -31, -488, -792, 780, 676,
  71, 234, 754, -276, -416, -418, 1185, -255, -287, 644, -255, 277, 318,
  -558, 317, 805, -49, 342, 446, -358, 743, 373, -529, 1364, -274, 496,
  -215, 324, 507, 193, -65, -226, 563, -35, -606, -911, -474, 363, 140, 280,
  -119, -47, -404, 518, 64, 366, -373, 518, 91, -465, -135, 18, 686, 475,
  854, 501, 613, 337, 384, -7, 235, -204, 1087, 419, -135, 172, 125, 166,
  671, -706, -1155, -330, 787, -773, -1429, -853, -511, 1342, 474, 1116,
  684, -685, 167, -99, -529, -76, -118, 186, 187, 634, 356, 218, -163, 453,
  -587, 79, 64, -306, 333, 475, -728, -117, 493, -207, 799, -295, 483, -137,
  645, 694, -238, -53, 648, 119, -282, 80, 365, -219, -133, -46, -156, -275,
  -203, 631, 273, -33, -94, 477, 401, 235]

theorem fractionalNearFrameSubtreeG2R0093_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0093Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0093Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0093Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0093_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0093LowerBoundTable : List ℤ :=
  [353, 1021, 1607, 582, -310, 2505, 32, 1700, 469, 2490, 1881, 989, -1376,
  2749, 2193, 2744, 3107, 532, 632, -1774, -492, -1721, 98, 1176, 6850]

def fractionalNearFrameSubtreeG2R0093LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0093Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0093LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
