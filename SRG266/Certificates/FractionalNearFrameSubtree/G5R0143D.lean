import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0143`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0143Mask : ℕ := 6917745282816529

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0143Witness : Array ℤ :=
  #[-70, -33, -89, -106, -79, 1, -39, -67, -61, -2, 27, 104, 103, 78, 128,
  58, -39, -22, -30, -49, -42, 53, 37, 38, 75, 43, 16, -64, -54, -62, 24,
  -47, 28, 50, 18, -67, 32, 0, -29, -99, -47, -18, -48, -3, -38, 39, 28,
  -29, 10, 4, -18, 2, -43, -27, 7, -4, -16, -10, 12, 29, 68, -8, -29, 50,
  -4, -9, 3, -14, -19, -6, -7, 22, 12, -15, -43, -13, 18, 7, 12, 44, -82,
  -41, -25, 22, -23, 25, 43, 43, 37, 6, -15, -13, 18, 2, 16, 12, 30, -14,
  -32, -10, -75, 93, 12, 33, 35, -38, -26, -17, 42, 5, -40, -55, -34, 5, 34,
  -56, 7, 99, -22, 3, -43, 21, 55, 11, 67, -15, -8, 5, 0, -32, 1, 11, 7, 16,
  0, 0, 57, -32, 17, -2, -11, 33, -7, -8, 9, 4, -24, 14, -58, -49, 49, 56,
  -54, 69, -26, -18, -21, 3, 22, 17, 0, 5, 0, -13, -31, 46, 38, 18]

theorem fractionalNearFrameSubtreeG5R0143_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0143Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0143Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0143Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0143_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0143LowerBoundTable : List ℤ :=
  [-82, 34, 3, -27, 51, 1, -92, -19, -85, 135, -62, 108, 71, 134, 153, -51,
  -157, 10, -48, -45, 74, -159, 149, 156, -9]

def fractionalNearFrameSubtreeG5R0143LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0143Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0143LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
