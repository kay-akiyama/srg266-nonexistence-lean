import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0089`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0089Mask : ℕ := 936554773783116

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0089Witness : Array ℤ :=
  #[64, 56, 75, 1, 84, -130, -47, -18, -61, 42, -40, 32, 3, -5, 60, 65, 81,
  1, 75, -12, -42, -30, -24, 56, 0, -74, -61, 6, -70, -9, -14, -60, 51, 168,
  29, 169, -44, -26, 82, -9, 62, -4, -12, -45, -24, 72, 85, -17, 36, -44,
  71, 35, 27, -28, 6, -33, -48, 41, 38, 30, 1, -49, 49, -26, 21, -21, 30,
  52, 26, 42, 43, 48, -6, -10, 65, -21, 62, 2, 31, 10, 78, 16, -18, 73, 49,
  77, -31, -45, 4, -16, 91, 80, 20, 78, 7, -65, -79, 76, 87, -20, 13, 30,
  11, 3, -17, -83, -37, -86, 25, 27, -44, -2, 3, 129, -6, -48, -67, 118, 11,
  9, 4, -69, 47, -27, -65, 31, 105, -56, -20, -58, 84, 9, 16, -11, -30, 31,
  6, -39, -18, -3, 46, 18, -30, 4, -50, 56, -91, -31, -32, -103, -5, 100,
  -4, 14, -21, -36, -6, -1, 58, 96, -1, 76, 34, 0, 26, 75, 36, -48]

theorem fractionalNearFrameSubtreeG1R0089_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0089Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0089Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0089Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0089_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0089LowerBoundTable : List ℤ :=
  [78, 2, 234, 0, 90, 183, 191, 284, 91, 178, 125, 19, 9, 121, 10, 208, 40,
  114, 124, -41, 71, 138, -93, 138, 367]

def fractionalNearFrameSubtreeG1R0089LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0089Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0089LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
