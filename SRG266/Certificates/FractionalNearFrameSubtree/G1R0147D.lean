import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0147`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0147Mask : ℕ := 1039688390529828

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0147Witness : Array ℤ :=
  #[12, 18, -54, -15, -12, -26, -27, 63, 55, -57, -22, 13, 53, -13, 31, -1,
  -48, -13, -45, 13, -16, 76, -30, 75, -2, 12, -10, -53, 47, -64, -14, 77,
  -49, -93, -6, -47, 42, 36, 17, -76, -58, -10, -40, 16, -32, -17, 15, -22,
  -38, -42, 23, 45, -63, -9, -58, 23, 82, 33, 115, -47, 31, 40, 60, -19, 36,
  -3, -56, -32, 0, -19, 83, -44, 43, 14, -37, -20, 21, 34, 47, 5, -15, 17,
  -24, 4, -30, 98, -60, 44, 57, -35, 5, 17, 16, 32, 33, 46, -62, 36, -49,
  53, -2, 18, -58, -1, 0, 15, -15, 45, -5, 37, 54, 45, -27, -71, -26, -7,
  -6, -67, 1, -32, -23, -40, 59, 96, 46, 34, 7, 19, 25, -97, -11, 35, -34,
  49, 90, 44, 57, -3, -30, -16, -10, 16, 33, 1, -30, -101, -19, 26, -22, 37,
  118, 16, 21, 59, -3, 29, 7, -2, 15, -7, 29, 11, 30, -21, -19, 46, 1, 0]

theorem fractionalNearFrameSubtreeG1R0147_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0147Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0147Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0147Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0147_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0147LowerBoundTable : List ℤ :=
  [-5, 72, 2, 79, -18, 80, -8, 1, 10, 8, 58, 246, 219, -18, 27, 142, -63,
  226, -18, 385, 158, -22, 42, -11, -18]

def fractionalNearFrameSubtreeG1R0147LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0147Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0147LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
