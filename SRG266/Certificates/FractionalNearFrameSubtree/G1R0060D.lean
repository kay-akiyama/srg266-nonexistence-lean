import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0060`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0060Mask : ℕ := 758482250156305

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0060Witness : Array ℤ :=
  #[-2, 26, 19, -35, -58, -37, 0, -16, -17, -26, 0, 46, 51, 48, 69, 60, 104,
  55, 55, 28, 33, 32, -4, 20, -25, 0, 13, 17, -14, -57, -28, -60, -67, -25,
  -56, 31, 48, 13, -2, 12, -49, 41, -9, 90, 49, -47, -5, -14, -15, 12, -4,
  -1, 7, 5, -2, 34, 38, -33, 10, -19, 6, -22, -4, 53, -15, -25, 51, 4, 9,
  -33, -40, 30, -38, 46, -36, -3, -93, 28, 23, -4, 31, 13, 10, 34, 55, 13,
  -12, 64, 5, 10, 39, 4, 54, 2, 20, 33, 49, 16, 17, -26, 2, 12, 10, -7, 26,
  -13, -37, 0, -30, -12, 6, -9, 5, -17, -5, -25, 30, -35, 29, 33, -11, -11,
  19, -11, 0, -32, 7, 1, -10, 21, 23, 10, -4, 41, 1, 9, 7, -27, 19, 6, 0,
  -32, -42, -28, -4, -30, 2, 27, -10, -2, -7, 12, -17, -15, -36, 47, 37,
  -21, -58, 16, -12, 55, 38, -18, -29, -4, -18, -67]

theorem fractionalNearFrameSubtreeG1R0060_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0060Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0060Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0060Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0060_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0060LowerBoundTable : List ℤ :=
  [8, -58, 1, -10, 79, 147, 2, 201, 16, -93, 19, 8, -74, 129, 85, 156, -2,
  11, -40, 52, 10, 147, 106, 30, 51]

def fractionalNearFrameSubtreeG1R0060LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0060Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0060LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
