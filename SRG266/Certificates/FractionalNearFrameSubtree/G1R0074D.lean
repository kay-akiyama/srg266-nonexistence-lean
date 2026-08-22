import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0074`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0074Mask : ℕ := 883901419079953

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0074Witness : Array ℤ :=
  #[23, -16, 33, 63, -30, 27, 14, 53, 0, 13, 38, -103, -39, 37, -64, 5, 0,
  -53, 3, -20, -23, -47, -40, -52, -8, -30, -32, -90, 100, 112, 55, 116, 44,
  17, 55, 15, -57, -6, -35, -53, 36, 5, 4, -21, 35, 45, 0, -15, 35, 61, -64,
  -50, 3, 25, 0, -48, 8, 35, -61, 18, 22, 32, 16, -44, -45, -4, -10, 42, 7,
  88, -39, -15, -25, 11, 70, -76, 57, -22, -68, -2, 9, -57, -30, 27, 24, -1,
  -10, -54, 17, 16, -22, -6, -24, -28, -13, 31, 3, -43, -40, 11, -42, 5, -7,
  -37, 43, 4, 28, 7, 39, 27, 85, 6, 45, 56, 13, -1, 2, -15, 5, -17, 39, 30,
  4, -30, -20, -34, -15, 66, 49, 0, -1, 2, 22, 3, 22, -31, -5, -6, 34, -24,
  -29, 81, 39, -49, 18, 2, 61, 39, 2, 41, 58, 33, -45, -19, 2, -10, -29, 44,
  -35, 32, 3, 33, -63, -50, 54, -19, 88, -68]

theorem fractionalNearFrameSubtreeG1R0074_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0074Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0074Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0074Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0074_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0074LowerBoundTable : List ℤ :=
  [1, 65, 39, 14, 2, 8, 26, 1, 86, 273, -39, 233, 112, 85, 23, 177, 10, -18,
  -63, 116, -143, -179, 133, 81, 11]

def fractionalNearFrameSubtreeG1R0074LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0074Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0074LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
