import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0050`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0050Mask : ℕ := 554993272328432

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0050Witness : Array ℤ :=
  #[-16, -48, -25, -20, -106, 134, -7, -25, -87, -46, 119, 113, 109, 175,
  90, 44, 21, 54, -27, 151, 61, -56, -121, -72, 34, 75, 58, 111, -5, 32,
  -56, -155, 9, -64, 108, 52, -82, -65, 0, 0, -60, -48, -73, -66, -183, -29,
  55, -14, 24, 44, -41, 39, 77, 0, -96, -40, 12, -136, 213, 93, -2, 4, 0,
  -11, 2, 24, -57, -8, -21, -132, -38, 144, -10, -58, -28, -48, 26, 55, 81,
  -159, -61, 54, -52, 3, 70, -19, -63, 34, -30, 131, 68, 136, 26, 61, -17,
  45, -188, 74, 69, 30, 107, 122, 54, 109, 83, 5, -19, 225, 201, 21, 69,
  105, -63, -24, -50, 52, 78, -115, -211, -194, -93, -45, 7, -163, -157, 35,
  39, -57, -22, 76, -50, -63, 45, -33, -17, 44, -63, 72, -37, -27, -109, 87,
  36, -78, -73, 74, -6, 46, 45, -24, -91, -35, 18, -65, -1, 92, -64, -47,
  -120, 35, -88, -137, -63, 36, -41, 105, 130, 108]

theorem fractionalNearFrameSubtreeG1R0050_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0050Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0050Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0050Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0050_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0050LowerBoundTable : List ℤ :=
  [-134, -148, -145, 198, 63, 1, 1, 72, -37, 195, -252, -85, -441, 139, 158,
  -29, -147, 559, 95, 11, 12, 228, 369, 69, 287]

def fractionalNearFrameSubtreeG1R0050LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0050Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0050LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
