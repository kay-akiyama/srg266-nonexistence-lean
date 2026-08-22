import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0089`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0089Mask : ℕ := 2508636882113170

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0089Witness : Array ℤ :=
  #[-8, 54, -9, -96, 39, -20, 103, 174, 4, 174, 81, -127, -78, -86, -187,
  -129, -82, 73, -84, -43, -48, 44, -92, 41, -71, -88, 61, 135, 115, 173,
  28, 17, -29, 68, 27, 28, -6, -40, -34, 24, -28, 86, -13, -18, -47, -13,
  64, 72, -75, 48, 38, 14, -61, 24, 76, 70, 21, -4, -37, -43, 16, 24, -42,
  -54, -68, -24, 22, 10, 40, -46, 17, -50, -17, 7, 73, 32, 28, 23, 1, -14,
  65, 42, -56, 88, -59, 52, 49, 37, -18, 40, 1, -24, -81, 15, -28, 72, -63,
  80, 3, 24, 21, -15, 8, 97, 29, -23, -10, 101, 32, 108, -128, -194, -131,
  -45, -23, -58, -4, -41, -2, 48, 52, 9, -75, -15, 86, 42, -152, -82, 0, 5,
  -5, -105, -57, -34, -41, -61, -60, 59, 23, 104, -103, 4, 0, -99, -110, 74,
  13, 92, 32, -36, 33, -44, 25, 13, 20, 57, 14, 5, -29, 33, -44, 93, 38, 76,
  19, 59, 28, 29]

theorem fractionalNearFrameSubtreeG3R0089_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0089Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0089Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0089Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0089_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0089LowerBoundTable : List ℤ :=
  [-58, -21, 71, -25, -144, 102, 25, 1, 15, 10, 125, 11, 11, 214, 84, 166,
  27, 11, 80, -188, 100, -49, 19, 209, 248]

def fractionalNearFrameSubtreeG3R0089LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0089Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0089LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
