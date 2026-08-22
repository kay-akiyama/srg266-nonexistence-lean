import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0073`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0073Mask : ℕ := 883899540089105

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0073Witness : Array ℤ :=
  #[-5, 35, 82, -37, 79, 43, 93, 58, 78, 39, 24, 68, -123, -132, -108, -55,
  -234, -196, -119, -22, -61, -90, -19, -61, 112, 109, 22, 7, 4, 0, 56, 112,
  0, -38, -65, 18, 31, 21, -25, -2, 52, 52, -60, -76, 45, -3, 6, 25, 15, -7,
  22, -30, 85, 28, 94, 29, 20, -87, 40, 61, 9, -82, -21, 90, 17, 6, 39, 57,
  18, 24, -13, -22, 3, -37, 77, 31, -49, 13, 16, 113, 50, 71, 28, 100, 28,
  93, 106, 67, 64, -25, 14, -62, 39, -22, 4, -59, -7, -45, 37, 19, 3, -2,
  65, 8, 31, -35, -6, -32, 9, -29, -16, 39, -5, 80, -69, -8, 15, 35, 57,
  -27, -4, -49, -24, -32, -50, 67, -68, 28, -54, 112, -46, 34, 35, 24, -59,
  25, 12, -15, 69, 95, -53, 99, 95, 7, -21, 32, 44, -6, 26, -1, -34, -1,
  -125, -114, 106, -34, 100, -13, -10, 106, -15, 80, 54, 168, 130, 35, 138,
  -25]

theorem fractionalNearFrameSubtreeG1R0073_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0073Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0073Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0073Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0073_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0073LowerBoundTable : List ℤ :=
  [47, 261, 275, 3, 2, 141, 40, 186, 2, 173, 210, 342, 138, 359, 442, 187,
  288, 130, 224, 148, 106, -114, 236, -203, 11]

def fractionalNearFrameSubtreeG1R0073LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0073Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0073LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
