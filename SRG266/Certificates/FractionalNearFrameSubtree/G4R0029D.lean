import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G4R0029`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0029Mask : ℕ := 5369656532978185

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0029Witness : Array ℤ :=
  #[-14, -73, -95, -60, -76, -106, -196, -481, -256, -152, -282, 364, 271,
  287, 124, 434, -132, 0, -42, 164, 152, -14, 125, -40, -428, -135, 50,
  -194, -72, 110, -156, -147, -120, -7, -130, -238, 21, -61, 249, 48, 0,
  278, -1, 2, 121, 199, 161, -167, 97, 127, 192, 55, -41, -46, -34, 0, 11,
  -88, -61, 18, -32, 14, 169, 178, 211, 196, -214, -178, 45, 24, -64, 107,
  129, -101, -100, -244, -91, 147, -69, -17, 107, 71, 366, 71, -54, -13,
  -196, -182, -98, -124, -202, 168, -66, 60, 68, -9, 229, -52, 127, 77, 230,
  -53, -57, -118, -43, -159, -17, 17, -371, -79, 73, 44, 74, 168, 33, 16,
  -114, -103, 172, 79, -101, -52, -215, 126, -147, 146, -104, -46, -14,
  -175, -569, 174, 143, 232, 194, 125, -312, 82, 118, -205, -196, 209, -131,
  239, -105, -88, 131, -132, -172, 99, -166, -87, 371, -158, 108, -161, 104,
  135, -91, 88, 53, 57, 139, -200, 116, 87, 138, 28]

theorem fractionalNearFrameSubtreeG4R0029_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0029Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0029Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0029Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0029_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0029LowerBoundTable : List ℤ :=
  [-276, 1, 2, 2, -263, -13, 3, 2, -114, 10, 478, -588, 579, 11, -295, -724,
  653, 263, 720, -853, 204, -189, 323, 184, 152]

def fractionalNearFrameSubtreeG4R0029LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0029Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0029LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
