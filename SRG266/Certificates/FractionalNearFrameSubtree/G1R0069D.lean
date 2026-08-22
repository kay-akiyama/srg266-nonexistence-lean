import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0069`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0069Mask : ℕ := 859735785589257

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0069Witness : Array ℤ :=
  #[-13, -28, 37, 0, 51, -3, 11, 58, 65, 0, 45, 9, -67, -50, -23, -26, -30,
  -24, 56, 35, 27, 18, 15, -43, 18, -2, -21, -5, 27, 38, -27, 85, 19, -39,
  3, 26, -65, -1, 8, -1, -35, 35, 14, 0, 28, 24, 20, -84, 4, -10, -22, -37,
  -4, 24, 100, -37, 20, 15, 29, 27, -46, 7, -9, -32, -31, 49, -19, 25, -35,
  -6, 12, 25, 59, 2, 15, -43, 40, -47, -53, -10, 3, -13, -9, 29, 39, -28,
  10, 50, -1, 12, 2, -58, -3, 0, -29, 9, -63, 57, -67, 4, 22, -20, -60, -1,
  -22, -16, -2, -64, 25, -52, -66, -33, -4, -2, 18, -10, -16, -19, 21, 16,
  41, 0, -5, 59, 44, 14, 55, 5, 97, -44, -9, 55, -28, 19, -2, 11, -38, 26,
  1, -36, 54, -37, 95, 78, -12, 16, -89, 0, -26, 33, 20, -42, -99, 19, -58,
  92, -35, 52, -5, 7, 53, -1, -28, 35, 4, -4, -41, -32]

theorem fractionalNearFrameSubtreeG1R0069_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0069Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0069Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0069Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0069_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0069LowerBoundTable : List ℤ :=
  [-29, 2, 1, 89, -30, 61, -146, 53, 100, 186, -91, 10, 171, -132, 21, 91,
  -38, 17, 13, 44, 10, 11, 151, 43, -82]

def fractionalNearFrameSubtreeG1R0069LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0069Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0069LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
