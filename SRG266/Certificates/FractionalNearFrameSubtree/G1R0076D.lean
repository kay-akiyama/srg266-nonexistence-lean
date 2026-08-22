import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0076`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0076Mask : ℕ := 890423394027793

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0076Witness : Array ℤ :=
  #[77, 53, 91, 87, 78, 18, -89, -83, -40, -115, 33, -87, -75, -46, -83, 30,
  81, -62, 71, 37, 23, -15, 3, -138, -49, -32, -8, -53, -41, -31, 29, 129,
  36, 7, -4, -13, -73, 79, 89, 27, -72, -50, -93, -49, 151, 50, 43, -125,
  -89, 25, 27, 137, -50, -15, 5, -126, 18, 40, -105, -70, -65, 40, 14, 33,
  14, -86, -60, -17, 33, 15, 86, -20, 18, -29, 110, -59, 61, -37, 26, 46, 1,
  -96, 16, -96, 43, 59, -24, -72, 20, -20, 15, -3, -16, -41, -48, 85, -54,
  -20, -22, -32, -8, 16, -58, 19, -82, 47, 38, -5, 24, -5, -48, 2, 57, 75,
  140, -55, -47, 39, -18, 76, -26, 17, 164, -81, 11, 44, 14, 0, -4, 46, 47,
  -80, 25, 10, -10, 52, -44, 50, -20, 32, -19, 51, 29, 83, -8, -70, -54,
  -181, 73, -32, -36, 2, 38, 23, -34, -12, 0, 5, 4, -16, -50, 3, 54, 11,
  -22, -61, 96, -168]

theorem fractionalNearFrameSubtreeG1R0076_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0076Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0076Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0076Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0076_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0076LowerBoundTable : List ℤ :=
  [-88, -41, 1, 57, -102, -58, -143, 2, 3, 230, -83, -95, 187, -80, 79, 34,
  -168, 7, 62, 111, -97, -192, 266, 19, -233]

def fractionalNearFrameSubtreeG1R0076LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0076Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0076LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
