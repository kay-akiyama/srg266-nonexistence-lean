import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0084`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0084Mask : ℕ := 929966025458252

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0084Witness : Array ℤ :=
  #[67, 11, 59, -24, 7, 45, 24, 6, 40, -115, 25, 53, 22, 61, 64, 70, 41, 10,
  57, -20, 46, 8, -26, -105, 42, 61, 32, -77, -34, -9, -50, 1, 52, 101, 12,
  15, 43, 18, -8, 41, -11, -19, 45, -51, -67, -47, 109, 0, 28, 80, -42, -48,
  34, 31, -40, -19, 18, -68, 17, 12, 34, -73, -18, 2, -12, -6, 38, 69, 20,
  -6, 42, 13, 65, -49, -1, -23, -59, 25, -61, 17, 64, 18, -54, 50, 33, -2,
  -7, 22, -20, 11, -9, 39, 32, -8, -30, 15, -72, -44, -45, -14, -6, 13, 4,
  -14, 46, 138, 87, 57, -34, 66, -25, -16, 68, -22, 26, 37, 25, 116, 37, 16,
  -136, 89, -68, 14, 59, 68, 19, 40, 104, 74, -26, 76, 22, 102, 69, 17, 25,
  -20, -71, 47, 15, 14, -61, -54, 1, -9, -53, -84, 45, 29, 17, 69, 3, 106,
  62, 88, 42, 6, -13, -31, 42, 75, 35, -3, -40, -53, 77, 17]

theorem fractionalNearFrameSubtreeG1R0084_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0084Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0084Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0084Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0084_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0084LowerBoundTable : List ℤ :=
  [99, 209, 34, 38, 88, 140, 156, 252, 278, 170, 297, 251, 440, -12, 116, 9,
  -20, 162, 84, 155, -3, 267, 132, 94, 456]

def fractionalNearFrameSubtreeG1R0084LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0084Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0084LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
