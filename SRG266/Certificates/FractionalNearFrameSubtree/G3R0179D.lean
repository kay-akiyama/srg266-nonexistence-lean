import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0179`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0179Mask : ℕ := 6865887702140050

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0179Witness : Array ℤ :=
  #[17, 81, -54, -19, 6, 22, 91, 104, 155, 69, 122, -143, -167, -113, 0,
  -97, 0, -36, -5, -48, 35, -8, -37, -13, 32, -41, 28, 78, 129, 18, 37, 47,
  61, -46, -32, 1, -28, -8, 43, -18, -42, -25, -37, -35, 37, 66, 69, 65,
  113, 118, -90, -51, 0, -94, 31, -3, -1, 19, -29, -32, 0, 44, -43, -75,
  -28, 26, -31, 112, -24, -10, -28, -34, -21, 64, 35, 35, -17, -46, 5, -21,
  -58, 65, -22, -1, 1, 50, 95, -20, -47, 9, -29, -54, 2, -26, -2, 53, 39,
  33, 15, -38, -20, 26, -3, -41, -59, -50, 37, 25, 95, 73, -37, 37, -28, 24,
  -127, -24, -1, 5, 80, 22, -13, 45, 17, 7, -65, -47, 22, -66, 1, -17, 31,
  27, 66, 12, -50, -47, 7, 39, 22, -8, -133, -82, -112, 41, 84, 73, -108,
  -57, -51, -16, 42, -88, -14, 11, 64, 16, 39, -44, 78, -4, 64, 73, -81,
  -26, -55, -44, 82, 64]

theorem fractionalNearFrameSubtreeG3R0179_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0179Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0179Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0179Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0179_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0179LowerBoundTable : List ℤ :=
  [-57, 3, 39, 2, 2, 48, 51, 3, -86, 34, 6, 179, 10, -66, 100, 10, 118,
  -218, 9, -40, 67, 255, 112, 381, -210]

def fractionalNearFrameSubtreeG3R0179LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0179Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0179LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
