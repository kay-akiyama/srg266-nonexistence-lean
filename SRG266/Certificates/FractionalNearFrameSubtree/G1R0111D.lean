import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0111`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0111Mask : ℕ := 968480255484322

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0111Witness : Array ℤ :=
  #[-98, 44, -43, -52, -63, -72, 95, 125, -18, 6, -114, 85, 46, 147, 23, 8,
  -79, 211, 0, 80, 37, 9, -65, 111, 66, 43, 0, 18, -50, 75, -79, -89, -127,
  -47, -9, -36, -8, 17, 38, 18, 17, 10, 75, 94, 90, 44, -34, 5, 32, 29, -45,
  -3, -35, 25, 47, 56, -82, -1, -65, -54, 14, 51, -32, 60, -46, 66, 95, -75,
  -5, -8, 26, -28, -48, 24, -2, 12, 26, 20, -75, 24, -4, -100, 32, 35, 74,
  45, 51, -30, -19, 25, 40, 66, 106, 38, -1, -12, -1, 32, -17, -39, 53, -31,
  49, -23, -29, 25, 51, 29, -101, -20, -6, 20, -48, -54, 13, -13, -30, 35,
  -14, 5, 46, 11, 27, -19, -77, -49, -17, -46, 27, -5, 92, -28, -14, 94,
  -21, -19, 19, 21, 33, 32, -6, 74, 11, -40, 20, -25, -6, 66, 37, 36, 12,
  -82, -70, -3, -16, 67, 34, -59, -17, -11, -44, 25, -79, 19, -105, -22,
  -164, 36]

theorem fractionalNearFrameSubtreeG1R0111_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0111Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0111Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0111Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0111_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0111LowerBoundTable : List ℤ :=
  [-14, -97, -67, 10, 80, 219, 1, 2, 318, -174, 62, -16, -14, 5, 120, 48,
  136, 99, -238, -93, 11, 109, 310, 30, 223]

def fractionalNearFrameSubtreeG1R0111LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0111Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0111LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
