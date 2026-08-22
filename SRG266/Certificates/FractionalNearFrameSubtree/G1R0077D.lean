import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0077`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0077Mask : ℕ := 890423771503633

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0077Witness : Array ℤ :=
  #[-138, -202, -100, 19, -85, -61, 48, 26, 68, 120, 92, 76, 0, 39, -4, 27,
  56, 36, -60, 85, -29, 39, -26, -2, 39, 8, 70, 20, -60, -73, 3, 115, -45,
  -46, 54, 89, -55, -165, -75, 12, 8, 39, 83, 125, 50, -17, 21, -9, 98, 24,
  12, 110, -4, -14, -32, -2, 25, 0, -23, 35, 38, 10, -23, -12, 78, -11, 10,
  80, 55, 21, -11, 7, 42, -31, -13, 79, 38, -4, 80, -4, -2, 41, 14, -109, 2,
  -37, -23, -32, 0, -32, -47, 27, -37, 16, 48, 47, -21, 94, 1, 25, -64, 3,
  -58, 1, 1, -28, 38, -14, 77, 2, 49, -12, 25, 43, 17, 65, 61, 129, -19,
  -33, 10, -39, -62, 34, 96, -72, 10, -18, 60, 97, -70, 33, 46, 6, 16, -37,
  -7, 105, -24, 9, -48, 29, -37, 7, 85, 39, 32, -122, 67, -15, 2, -16, 62,
  -68, -123, 19, -30, -22, -20, 43, -8, -17, -4, 25, -40, -19, 127, -139]

theorem fractionalNearFrameSubtreeG1R0077_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0077Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0077Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0077Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0077_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0077LowerBoundTable : List ℤ :=
  [35, 2, 147, 72, 95, 71, 71, 1, 2, 359, 117, 208, 174, 178, -74, 301, -18,
  102, 125, 216, 193, 8, 180, 73, -15]

def fractionalNearFrameSubtreeG1R0077LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0077Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0077LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
