import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0089`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0089Mask : ℕ := 5508197066051082

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0089Witness : Array ℤ :=
  #[-33, -27, 22, -36, 37, -72, 0, 63, 0, 38, 35, 4, -13, 8, -38, 0, -104,
  -46, 14, -62, -104, 23, -17, -14, 8, 34, 14, 77, 27, 24, 32, 22, -42, -71,
  -36, -1, 36, 62, 67, -49, 41, -35, -46, 64, 24, 24, 12, -4, 45, 11, 45,
  33, -64, -24, -61, 19, 31, 4, 34, -37, 9, -32, 11, 20, -1, -7, -16, 9,
  -23, -53, 3, 57, -4, -18, 3, 8, 21, -31, -1, -4, -6, -26, 52, -33, 18, 27,
  -22, -1, 1, -27, 8, -26, 60, -49, -32, 22, 4, 7, 34, 20, 43, 15, 75, 10,
  25, -18, -3, 32, -6, -26, 4, -45, 16, -2, -43, 47, -2, 33, -3, -16, -81,
  -20, 13, 33, -9, 30, -49, -54, -12, 5, -50, -8, -8, 5, -4, -37, 6, -98,
  25, -24, -8, 33, 21, 8, -34, 62, 11, -31, -20, -5, -20, -26, -21, -17,
  -14, 8, 3, 18, 23, 5, -10, 0, -5, 51, 8, 16, 16, -1]

theorem fractionalNearFrameSubtreeG5R0089_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0089Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0089Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0089Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0089_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0089LowerBoundTable : List ℤ :=
  [-43, -60, 23, 20, -56, 2, 2, 4, -32, 34, -42, 10, -11, 72, 178, 95, -119,
  10, -52, 74, -166, 8, 47, 49, 11]

def fractionalNearFrameSubtreeG5R0089LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0089Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0089LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
