import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0092`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0092Mask : ℕ := 939854283713316

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0092Witness : Array ℤ :=
  #[-10, 72, 35, -8, 15, 51, 15, -33, 78, 17, -18, -78, -85, -18, -46, 3,
  28, -11, -28, 0, -61, -20, -61, 8, 31, 80, 87, 38, 25, -22, -57, 18, 39,
  14, 49, 27, 54, -66, 57, 74, 47, 39, 3, 38, -12, -15, 27, -39, 12, -1,
  -31, -7, 68, 15, -27, 0, 17, -16, 0, 15, -37, -59, -29, -27, -13, -22, -2,
  22, 78, 10, 25, 24, -14, 44, 11, 46, 21, -30, -24, -37, 13, -12, 23, 0,
  26, 21, -57, -18, -29, 19, 29, -46, 20, 28, 15, 23, -6, -49, -26, 72, -15,
  -35, 12, 0, 36, 29, 43, 50, -34, -31, -5, -15, -59, -15, -11, -33, 10, 18,
  16, -67, 36, 83, -49, -32, -67, 0, 86, 23, 39, -56, -1, 0, -36, 19, -28,
  11, 4, 37, -15, 17, -35, -5, 42, -4, -97, 2, -26, -39, 94, 6, -14, -49,
  16, -44, 59, 29, 126, 0, -25, 40, -60, 32, -27, -3, 8, 16, 62, -13]

theorem fractionalNearFrameSubtreeG1R0092_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0092Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0092Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0092Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0092_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0092LowerBoundTable : List ℤ :=
  [-2, 1, 31, -80, 22, -7, 97, 2, 115, -54, 210, 9, 9, 16, 78, 83, 96, 49,
  56, 159, 190, 25, -31, 251, 63]

def fractionalNearFrameSubtreeG1R0092LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0092Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0092LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
