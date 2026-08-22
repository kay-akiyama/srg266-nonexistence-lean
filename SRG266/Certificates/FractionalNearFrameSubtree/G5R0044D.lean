import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0044`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0044Mask : ℕ := 4737714362368131

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0044Witness : Array ℤ :=
  #[2, 25, 21, 4, 9, 15, 7, -27, 27, 13, -19, -21, -18, 0, 30, 11, 12, -11,
  -7, 24, -5, 0, -18, 0, 0, 33, -1, 22, 11, -15, -2, -4, 48, -6, -19, 22, 1,
  -24, 32, -6, 7, 26, 8, 9, 12, 14, -12, 13, 6, -14, -30, -11, 12, -37, 0,
  -8, -20, 20, 4, -15, -8, -14, 16, 38, -14, 35, 7, 28, 23, -14, -34, 24,
  23, 17, -5, 28, 24, 39, -24, -1, -17, 29, 47, 31, 2, 1, 10, 7, -17, 36,
  -7, -29, 27, 0, -14, 32, 9, 12, 13, 10, -58, 13, 8, 0, -6, -3, -6, -4,
  -31, 2, -56, -5, 19, 12, 15, 12, 18, 18, -8, -25, 3, -9, -17, 8, 14, -4,
  -33, -15, -28, -16, 9, 44, -14, 16, 4, 5, 3, 9, 9, 21, -16, -13, -16, 31,
  -42, -33, 26, 2, 23, 3, 2, 20, 21, 1, -7, 4, 1, 4, 9, -14, 8, 20, 31, 1,
  18, -2, -2, -29]

theorem fractionalNearFrameSubtreeG5R0044_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0044Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0044Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0044Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0044_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0044LowerBoundTable : List ℤ :=
  [2, 3, 36, 8, 43, 17, 89, 74, 1, 103, 55, 3, 57, 9, -20, 84, 24, 122, 21,
  133, 3, 144, 20, 50, 77]

def fractionalNearFrameSubtreeG5R0044LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0044Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0044LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
