import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0043`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0043Mask : ℕ := 538509888504020

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0043Witness : Array ℤ :=
  #[29, -2, -23, 4, -5, 42, 26, 47, 48, 26, 3, -12, -34, -18, 23, 70, 16,
  -34, 29, 37, 47, -14, -33, -13, 19, -6, 25, -9, -10, -39, -53, 24, -120,
  -32, 30, 102, 6, -41, 2, -20, 91, 71, 30, 40, 52, 2, 7, -17, -21, -68, 33,
  -31, 40, -37, 0, -39, -65, 8, -11, 12, 2, 6, 32, -9, -14, 24, -5, 12, -2,
  11, -8, 16, 0, 47, -12, -10, -2, 19, -36, 4, 20, 11, 8, -41, 9, 17, 0, 10,
  23, -43, 47, 0, -45, -35, 4, 18, 19, 13, 63, -23, -16, 4, 11, 14, 2, -7,
  13, -30, 58, 60, -9, -57, -54, 64, 21, 0, -13, 13, 27, 13, -11, 17, 42,
  -38, 34, -32, -52, 24, 51, -13, -1, 24, -18, 57, -77, 4, -13, 40, 4, 22,
  -15, 16, -28, 26, 1, -12, 41, -21, -4, 7, 10, 22, 29, 26, 44, -50, -28, 2,
  17, -38, 26, 18, -16, -4, 3, -8, -3, 5]

theorem fractionalNearFrameSubtreeG1R0043_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0043Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0043Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0043Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0043_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0043LowerBoundTable : List ℤ :=
  [14, 28, 14, 55, -1, -10, 82, 39, 39, 89, 71, 123, 60, -35, 57, -17, 33,
  44, 58, 168, -40, 133, 106, 188, 278]

def fractionalNearFrameSubtreeG1R0043LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0043Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0043LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
