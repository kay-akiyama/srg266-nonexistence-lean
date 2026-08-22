import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0077`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0077Mask : ℕ := 5438856987583238

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0077Witness : Array ℤ :=
  #[-71, 51, 64, 75, -90, -19, -103, -77, -44, -106, -37, 110, 33, 86, 88,
  92, -45, 68, 14, -60, -13, 77, 0, 51, 15, -52, 3, 29, -43, -12, 0, -6, -8,
  -5, -25, 14, 3, -17, 34, 106, 47, 0, 39, -16, 10, 78, 28, -25, -44, -8,
  18, -46, 29, -2, 19, 13, -66, -49, 19, 35, 21, -26, 38, 17, -41, -8, 36,
  -6, -22, 30, -4, -2, -95, 4, -35, -101, -8, -6, 92, -4, -59, 1, 2, -15,
  14, -80, 27, 29, 6, -34, -42, -47, 88, 28, 79, 88, 27, -42, 32, -42, 30,
  30, 33, 29, 44, 14, 22, 172, 16, 28, 57, -56, -20, -32, -75, 0, 73, 4, 32,
  -19, 46, 20, 62, -8, -19, 101, 80, 111, 48, -23, -10, 19, 31, 11, -21, 13,
  40, 7, -26, -45, -41, 37, -33, 67, 58, -24, -11, 56, 23, 0, 0, -11, 14,
  -102, -21, 35, -20, -78, 69, -75, -86, -58, -26, 44, 9, -16, -42, -3]

theorem fractionalNearFrameSubtreeG5R0077_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0077Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0077Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0077Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0077_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0077LowerBoundTable : List ℤ :=
  [-2, 35, 2, 55, 1, -35, 204, 89, 12, 9, 174, 214, 75, 219, 91, 259, -79,
  -78, 9, 270, -23, 64, 8, 10, 265]

def fractionalNearFrameSubtreeG5R0077LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0077Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0077LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
