import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0026`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0026Mask : ℕ := 953951320900678

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0026Witness : Array ℤ :=
  #[-5, -144, -203, -225, -46, -35, 5, -11, 74, 0, -17, 120, 151, 47, 71,
  32, 146, 76, -86, 36, 43, 26, -14, -1, 0, -77, -87, 33, -83, -30, -17, 68,
  -18, -38, -164, 21, 55, -21, 0, -85, -80, 18, 11, -2, -92, 112, -161, -64,
  -104, -182, -75, -71, 157, 99, 47, 35, -57, -75, 70, -22, 8, 30, -15, 71,
  107, 34, 51, 77, -107, 48, 60, -26, 98, 125, 16, -51, 46, 31, 77, 50, 31,
  106, 91, 157, 160, 88, 72, -147, 59, 59, 68, -29, -48, -57, 93, 22, 67,
  -54, -2, 76, 21, -33, -56, -135, 31, -118, -2, -1, -4, -6, -93, -67, 40,
  58, -19, -47, -33, -38, -51, -90, -100, 45, -31, -19, -19, -122, 5, -4,
  23, 11, 5, -125, -46, -62, -81, -15, 0, -27, 107, -75, -83, 99, -52, -43,
  14, 48, 22, -106, 99, -109, -9, -140, 80, -57, 89, 10, 50, 46, -24, 88,
  -61, -21, -26, -42, -39, 14, -153, 10]

theorem fractionalNearFrameSubtreeG3R0026_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0026Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0026Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0026Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0026_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0026LowerBoundTable : List ℤ :=
  [-204, -165, -150, -10, 24, -237, 2, 149, -125, -283, -294, -154, -95,
  246, -43, 115, 8, 445, 11, 10, 243, -35, 39, -155, 10]

def fractionalNearFrameSubtreeG3R0026LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0026Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0026LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
