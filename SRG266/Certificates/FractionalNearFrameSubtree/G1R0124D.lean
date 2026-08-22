import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0124`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0124Mask : ℕ := 969526865939240

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0124Witness : Array ℤ :=
  #[48, 54, 16, 43, -10, 23, -80, 22, -41, -29, 28, -56, -36, 37, 0, -19,
  -80, -38, -29, 32, -86, 20, 63, -7, -5, 18, 66, 33, 10, 22, -11, 6, 123,
  19, -13, -48, 52, 24, -13, -107, 8, 8, -10, -18, 120, -33, -23, 26, 14,
  64, -38, 7, -160, -53, -105, 95, 42, -10, 2, -15, 38, 9, 110, 7, -20,
  -103, 56, -51, 2, 15, 15, 16, -72, 136, 4, 125, -7, 10, 24, -28, -20, 2,
  40, 114, -80, 38, 0, -8, -11, -9, 79, 11, -162, 7, 76, -12, 23, -8, 91,
  -79, 5, -39, -73, 39, -6, 14, -9, 77, 93, 87, -99, -140, 0, -68, -95,
  -112, -4, -24, -11, -42, 256, 78, 2, 7, 87, -21, -43, 19, -43, -5, -53, 3,
  97, -13, -121, -42, -49, 2, -7, 29, 132, 1, 53, -29, -36, 47, 10, 38, 34,
  29, 49, 92, 16, 61, -38, -28, 23, -68, 105, -40, -1, 57, -54, 0, 40, 44,
  -168, 115]

theorem fractionalNearFrameSubtreeG1R0124_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0124Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0124Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0124Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0124_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0124LowerBoundTable : List ℤ :=
  [-13, 45, -28, 47, -55, 158, 1, -52, 107, 129, 9, 80, 125, 378, 156, 54,
  9, 9, 59, 47, 126, -22, 10, 42, 204]

def fractionalNearFrameSubtreeG1R0124LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0124Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0124LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
