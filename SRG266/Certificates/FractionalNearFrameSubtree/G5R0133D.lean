import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0133`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0133Mask : ℕ := 6034501305049506

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0133Witness : Array ℤ :=
  #[106, 456, 47, -138, 302, 508, 254, 209, -17, 160, 0, -558, 110, -106,
  -665, -309, 41, 432, -5, 8, 384, -102, 41, -122, -271, -181, 244, 225,
  -226, -158, -358, -386, 330, 258, 126, 256, 0, 329, 132, 72, 252, -82, 63,
  -64, 142, -10, -88, 265, 240, -27, 2, -139, 72, -408, 218, -219, 210, 221,
  -77, -317, -172, -261, 79, 114, 123, 86, 95, 323, -96, -125, 176, -143,
  199, 265, -39, -232, 130, 199, -367, -30, 287, 89, -54, 310, -108, -321,
  -136, 156, -55, 174, -211, -12, -268, 21, -3, -5, 190, -279, -81, -24,
  -230, -236, -222, -82, -156, 166, 87, -148, 193, -84, 182, 29, -35, 161,
  109, -8, 244, 161, -62, 158, 27, 89, 84, -43, 174, 79, -104, 0, -268, 239,
  95, -340, 110, -10, -135, 69, 72, 355, 178, 0, 328, 193, -43, -34, 404,
  108, -292, 112, 86, -122, 15, 30, -98, -37, 99, 11, 363, 12, 95, -24, -93,
  70, -182, 75, -355, -32, 119, 380]

theorem fractionalNearFrameSubtreeG5R0133_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0133Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0133Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0133Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0133_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0133LowerBoundTable : List ℤ :=
  [-122, 417, -60, -110, 494, 306, 3, 1, 487, 10, 213, 682, 1486, 876, -74,
  494, -448, -212, -545, 429, 1225, 10, 514, 1203, 1385]

def fractionalNearFrameSubtreeG5R0133LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0133Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0133LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
