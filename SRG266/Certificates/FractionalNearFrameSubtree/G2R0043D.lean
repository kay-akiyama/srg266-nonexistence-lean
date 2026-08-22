import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0043`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0043Mask : ℕ := 901165343289889

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0043Witness : Array ℤ :=
  #[0, 4, -27, -34, 30, -77, 33, -33, 4, 12, 14, -35, 0, 3, -3, -11, -15,
  -23, -44, 33, 44, -12, -15, -73, 55, 30, 35, 24, -4, -68, -41, 16, -7, 8,
  24, -47, 74, 4, -12, -16, 34, 26, 4, 0, 41, 7, 63, 0, -1, 9, 39, -47, -52,
  -22, 18, -74, 0, 100, 16, -13, 10, -21, 0, 59, 20, -39, -55, 2, 18, -68,
  -29, 16, 8, 9, 35, 2, -1, 0, 10, -2, 33, 36, 0, 23, 7, 27, 22, -50, -89,
  -45, -55, 89, 47, 32, 52, -47, -2, -39, 68, -14, -4, 62, 29, -50, 28, 29,
  -7, -14, -35, -69, -48, -14, -30, 16, -11, -21, 75, 8, 9, -32, -31, -48,
  -5, -35, 8, -8, -62, -8, -9, -10, 71, 16, -40, 5, 20, 2, 4, -17, 20, 4,
  12, 12, -15, 5, 8, 18, 29, -25, -30, 33, 40, 12, 4, -3, -11, -23, -6, -8,
  76, -42, 11, 69, -29, 12, -7, 42, -2, -68]

theorem fractionalNearFrameSubtreeG2R0043_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0043Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0043Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0043Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0043_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0043LowerBoundTable : List ℤ :=
  [-44, 30, 55, 42, -82, 1, 2, -89, 4, 8, -52, 76, -96, 93, 169, 78, 10,
  -18, 176, 10, 32, 11, 12, -78, -33]

def fractionalNearFrameSubtreeG2R0043LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0043Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0043LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
