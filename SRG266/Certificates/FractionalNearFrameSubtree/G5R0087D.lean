import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0087`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0087Mask : ℕ := 5473457780990292

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0087Witness : Array ℤ :=
  #[51, -26, 16, -74, -16, 32, -38, -16, 34, 4, -64, 84, 0, 24, 54, -22, 56,
  -47, 9, 44, -40, 33, -32, -31, 15, -39, 2, 15, 20, -58, 71, 104, 15, 14,
  -15, -39, -4, -45, -1, 0, 0, 20, 5, -16, -53, 22, 7, 33, -3, -8, 66, 55,
  40, 18, -20, 28, 19, 30, -1, 10, 70, 31, 5, -29, -37, 45, 53, -29, -25, 5,
  -65, -58, 33, -20, 7, -13, 33, 30, 58, -75, -40, -12, -62, 5, -50, -62,
  -18, -6, -28, 1, -49, 39, 14, 47, 77, 13, 23, 10, 15, -2, -9, -39, -5, -1,
  -44, 38, 24, 17, -6, -6, -16, -20, -37, -5, -33, -25, 36, 18, 55, 27, 18,
  3, -15, -13, 21, 6, 12, 14, -6, -24, -11, 27, 13, -58, -6, -39, 36, 5,
  -28, -23, -28, 2, 0, -30, 8, 1, 20, 12, 5, 13, -15, -36, -15, -53, 8, 40,
  -45, -37, 0, -30, -44, 10, 10, -66, -12, -48, -41, 0]

theorem fractionalNearFrameSubtreeG5R0087_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0087Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0087Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0087Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0087_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0087LowerBoundTable : List ℤ :=
  [-86, -83, -73, -41, -136, -26, 57, 42, 41, 9, -70, 113, -56, 132, -5, 38,
  9, -192, 228, 147, 9, -7, 9, 20, 165]

def fractionalNearFrameSubtreeG5R0087LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0087Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0087LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
