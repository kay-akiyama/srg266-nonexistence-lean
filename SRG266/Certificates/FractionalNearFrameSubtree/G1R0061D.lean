import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0061`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0061Mask : ℕ := 758488625303825

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0061Witness : Array ℤ :=
  #[83, 56, 105, 73, 8, 65, -143, -151, -119, -123, -76, -139, 21, 75, 31,
  76, 69, 90, 35, 11, 21, 38, 2, -3, -9, 1, 38, -19, -20, -25, 2, -54, -92,
  -26, -101, -31, 36, 90, 143, 114, -111, -26, -101, 0, 160, -43, -28, -42,
  11, 19, 9, -26, 24, 34, -8, 46, 8, 27, -39, 16, -30, -31, -1, 34, -11,
  -14, 37, 20, -29, -29, -8, -3, 4, -18, 10, 1, -11, -34, -28, -14, 9, 21,
  27, 13, 11, 5, 15, 7, -25, -18, 11, 10, 30, -2, 7, 15, 22, 32, 1, 0, 11,
  18, 22, 10, 12, -4, -5, 23, -16, -2, -8, -4, 19, -18, 8, 19, 36, 32, 0,
  -36, 26, -5, 10, -4, -3, 15, -12, 8, -3, -1, -3, -4, 19, 10, -1, 0, 3, 26,
  55, -36, -47, -20, -44, -28, 11, -2, -18, -22, -26, 14, 0, -2, -19, 24,
  10, 17, 25, 7, 16, 6, 18, 24, 19, -20, 10, 16, 18, -5]

theorem fractionalNearFrameSubtreeG1R0061_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0061Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0061Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0061Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0061_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0061LowerBoundTable : List ℤ :=
  [13, 0, -11, 2, 95, 70, 1, 1, 68, 32, 4, -16, 59, 28, 29, 106, -127, 106,
  39, 35, -22, 153, -188, 190, 9]

def fractionalNearFrameSubtreeG1R0061LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0061Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0061LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
