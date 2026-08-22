import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0234`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0234Mask : ℕ := 5091535437285897

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0234Witness : Array ℤ :=
  #[-79, 74, 99, 126, 187, 115, 139, 105, 29, 76, -37, 89, -190, -73, -150,
  -175, -146, -196, 60, -273, -169, -64, -72, 136, 80, -100, -130, 23, 137,
  129, 193, 225, -38, 22, 17, 58, 9, 14, -26, -14, -26, 12, -130, -2, -50,
  8, -48, 43, 47, 12, 34, -2, -18, -26, -12, -41, 76, 126, 36, 54, 109, 52,
  -69, -41, 28, 1, -155, 46, 98, 21, 17, 16, -27, 24, -89, -7, -34, 4, 108,
  -95, -88, -36, -43, -58, 18, -9, 19, 20, 50, 10, 66, -36, 8, -28, -47, 8,
  -80, -48, -41, -1, 40, 76, 85, -13, 103, -20, -49, 85, 55, 50, 53, -31,
  57, -53, 25, -67, -73, -113, 7, 24, -36, 20, 46, -72, 3, -78, 20, -39, 38,
  30, -9, 55, -56, -20, -29, 151, 1, -45, -52, 48, -55, 22, 31, 20, -73, -1,
  -12, 167, 82, 9, 68, 20, 124, -48, -9, -67, -2, 58, 55, -32, -74, 9, -28,
  -124, 25, 110, 16, -58]

theorem fractionalNearFrameSubtreeG2R0234_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0234Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0234Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0234Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0234_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0234LowerBoundTable : List ℤ :=
  [-66, 41, 31, 59, 92, 250, -165, 2, 51, 55, 10, 42, -82, -86, 270, -180,
  11, 84, 97, 226, 11, -32, 79, 154, 9]

def fractionalNearFrameSubtreeG2R0234LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0234Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0234LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
