import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0037`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0037Mask : ℕ := 537553314423186

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0037Witness : Array ℤ :=
  #[0, 0, -50, -33, -2, -59, 0, 102, 26, -19, -5, 61, 57, 35, 85, 7, 8, 23,
  31, 12, -11, -3, -4, 0, 61, 49, 15, 11, 1, 19, -8, -19, 33, 6, 17, 5, -19,
  23, -19, 21, -14, 28, 26, -31, -25, -36, 36, -16, 4, -13, -13, -11, 27,
  -4, 16, -26, -9, 10, 1, 3, 34, 30, -12, 11, 39, 15, 33, -47, -3, -28, 4,
  44, 18, 22, 0, 1, 9, 22, -3, 46, 9, 20, 20, 30, 5, 14, -1, 10, -3, -16,
  19, 2, 29, 11, 6, -23, -16, 26, 28, -21, 76, 40, 38, 14, 4, -5, 4, 14,
  -13, -76, -60, -44, -1, 2, 6, 3, 20, 29, 26, 45, 26, 13, -30, -36, -13,
  -45, 27, -35, -7, -12, -53, -2, 83, -49, 37, -12, -9, 0, 38, -12, -29, -6,
  12, 9, 0, 22, 2, -22, 29, 2, 29, 31, -29, -37, 43, 52, -14, 6, 1, -15, -4,
  -9, -1, 0, 6, -9, -13, -5]

theorem fractionalNearFrameSubtreeG1R0037_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0037Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0037Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0037Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0037_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0037LowerBoundTable : List ℤ :=
  [42, -10, -12, 129, 21, 116, 115, 206, 77, -19, 39, 145, -13, 105, -38,
  -32, 78, 159, 82, 11, 5, 11, -5, 75, 190]

def fractionalNearFrameSubtreeG1R0037LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0037Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0037LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
