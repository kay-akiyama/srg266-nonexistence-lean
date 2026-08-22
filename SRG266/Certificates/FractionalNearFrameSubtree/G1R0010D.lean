import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0010`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0010Mask : ℕ := 265907617616133

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0010Witness : Array ℤ :=
  #[19, 32, -50, -18, 16, -26, 16, -40, 34, 54, 53, 0, -35, -18, -41, -11,
  -9, 71, 36, 99, 14, 62, -14, 1, 45, -12, 46, -2, -53, -32, 2, 15, 20, -29,
  -32, -41, -8, -24, 15, 18, -36, -14, -17, 34, -10, 40, -26, -46, 86, 2,
  -23, 19, -22, 0, 27, -13, -28, -59, 84, -34, -29, 8, 11, 24, 14, -19, 57,
  -17, 16, 53, -20, -47, 56, 54, 18, 30, 32, 67, -36, 73, -12, 85, 50, 37,
  -28, 11, 4, 36, 31, -29, -14, -10, -4, 26, 19, 12, -20, -28, -16, 14, 31,
  44, -26, 28, 44, 30, 3, 21, -6, 26, 28, 39, -5, 44, 1, 30, 5, -25, -44,
  -14, 65, 72, 35, 51, 23, -101, 81, 8, -11, 65, -50, 3, 46, 2, 79, 35, -87,
  26, 93, -25, -5, -37, -7, -75, -21, -29, 0, -26, -42, -102, 73, -32, 4,
  -2, -64, 3, -28, 87, 44, 78, 36, -9, 5, 61, 32, -57, -39, -11]

theorem fractionalNearFrameSubtreeG1R0010_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0010Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0010Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0010Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0010_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0010LowerBoundTable : List ℤ :=
  [46, 2, 46, 257, 2, 2, 80, -18, 200, 98, 236, 101, 169, 6, 60, -59, 108,
  194, 214, 124, 512, -9, -3, 43, 11]

def fractionalNearFrameSubtreeG1R0010LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0010Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0010LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
