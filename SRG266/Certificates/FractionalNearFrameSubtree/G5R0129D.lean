import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0129`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0129Mask : ℕ := 5863472539074914

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0129Witness : Array ℤ :=
  #[28, 23, 23, 17, 9, 20, 0, -14, 30, -1, -10, -21, -16, -5, 8, 36, -30,
  72, 59, 66, 69, -27, -3, 27, -57, -36, -73, -60, 24, 24, 7, 45, 1, -15,
  -3, 0, -27, -10, 67, 38, 39, -24, 20, 42, 42, 10, -4, -18, 9, -29, -14,
  18, 11, 75, 9, -45, -20, -53, 64, 62, 51, 36, 18, -10, -39, -55, 1, -7,
  -16, 8, 8, 66, 7, -86, -35, 71, 46, -62, -45, 35, 5, 47, 82, 1, -5, 58, 9,
  2, 41, 39, 22, -11, -5, -48, -66, 44, 59, -54, 61, 18, -42, -16, 85, -31,
  -1, -45, 1, -63, -31, 34, -10, 34, 32, 26, -46, -43, -4, -29, 9, 14, 114,
  -46, 42, -33, 38, 19, -36, -30, -11, -10, 16, -42, -12, 60, 23, 94, 18, 5,
  15, -31, 71, 11, -33, -24, 76, 33, 34, -21, -78, 24, 17, 76, 15, 22, 4,
  -60, 14, 24, 64, 69, 27, 36, 44, 17, 84, -3, -19, -33]

theorem fractionalNearFrameSubtreeG5R0129_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0129Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0129Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0129Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0129_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0129LowerBoundTable : List ℤ :=
  [66, 133, 70, 102, 2, 68, 81, 219, 67, 101, -4, 300, 8, 11, 9, 229, 26,
  217, 178, 114, 171, 209, 68, -18, 153]

def fractionalNearFrameSubtreeG5R0129LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0129Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0129LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
