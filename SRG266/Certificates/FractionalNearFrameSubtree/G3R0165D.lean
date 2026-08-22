import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0165`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0165Mask : ℕ := 6856950408254552

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0165Witness : Array ℤ :=
  #[360, 190, 25, 125, 200, 116, -148, 112, -55, 80, -125, -110, -149, -218,
  277, 271, -124, 26, 109, 156, -251, 2, -91, -37, -104, 12, 89, -67, 18,
  62, 48, 61, 0, -87, -147, 147, 191, -270, -140, -169, 74, 47, -67, -205,
  -23, 230, 121, 199, 37, 206, -66, 166, 67, -68, 111, 85, -137, -92, 64,
  189, -174, 33, 248, 184, -261, 279, 51, -252, 300, 28, 7, 169, 215, 47,
  -163, -492, 249, -124, 159, -187, 88, -81, 266, -98, 149, -256, 137, 70,
  239, 116, -183, 95, -79, 10, 104, 397, 47, 216, -102, 173, -33, -85, -82,
  297, 229, 251, 298, 248, 0, 182, -246, -300, -175, -195, -242, -136, -56,
  30, 82, 394, 40, 147, 131, -241, 322, -186, 151, 26, 132, -102, -49, 146,
  -90, 201, 103, 17, 4, 105, 248, 115, -217, -28, -29, -68, -50, 74, -73,
  50, -252, 72, 135, 96, 120, 89, 170, 266, 38, -35, -50, -29, 175, 48, 103,
  -1, 0, 167, 225, 140]

theorem fractionalNearFrameSubtreeG3R0165_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0165Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0165Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0165Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0165_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0165LowerBoundTable : List ℤ :=
  [237, 497, 504, 460, 306, 419, 240, 713, 2, 240, 601, 914, 241, 355, -18,
  -83, 631, 177, -182, 1146, 86, 568, 608, 1082, 1015]

def fractionalNearFrameSubtreeG3R0165LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0165Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0165LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
