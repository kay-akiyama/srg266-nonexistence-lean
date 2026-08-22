import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G4R0023`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0023Mask : ℕ := 5159856228516099

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0023Witness : Array ℤ :=
  #[768, -1053, -310, 628, -224, 640, -1344, -157, -1373, -1305, -260, 1452,
  1181, 706, -434, 1537, -655, -764, -422, 1709, -774, 359, 1393, 1322, 719,
  121, 520, -1077, -919, 145, -1079, -919, 417, 206, 274, -485, -317, 525,
  411, 177, -740, -1399, 644, 1455, 731, 53, 716, -239, 768, 0, -776, 772,
  -229, 124, -530, 90, 315, -207, 554, 449, 752, 15, -683, 831, -1005, 449,
  -904, -307, 460, -265, 7, 539, 516, -385, 468, -128, 96, -248, 597, -233,
  -967, -140, -400, -193, -536, 219, 672, 750, 630, 975, 788, -814, -752,
  107, 825, 329, 921, 85, -394, 431, 109, -123, 547, -644, 119, -670, 770,
  -375, -380, -384, -1401, 520, 546, 168, -448, -157, 9, 640, -237, -1260,
  1336, -43, 105, -1021, -823, 0, 1170, 800, 285, -780, 297, -171, 15, 2032,
  689, -575, -367, -421, -680, 197, 642, -775, -633, 483, 1440, -495, -128,
  -25, 668, 348, 510, 497, -330, 115, 1754, 400, -781, -1158, 1125, -220,
  475, 965, 886, 1049, -108, -445, 0, -75]

theorem fractionalNearFrameSubtreeG4R0023_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0023Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0023Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0023Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0023_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0023LowerBoundTable : List ℤ :=
  [31, 1127, 536, -261, 654, 2291, 899, 625, -952, 2479, 2352, 2143, -1204,
  100, 496, 1827, 1512, 3285, 2628, 314, 3449, -1440, 3078, 1305, 3111]

def fractionalNearFrameSubtreeG4R0023LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0023Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0023LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
