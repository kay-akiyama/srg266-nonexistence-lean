import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0522`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0522Mask : ℕ := 6771569894005265

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0522Witness : Array ℤ :=
  #[-177, -141, -155, -145, -111, -95, 51, 48, 116, 23, 73, 72, 64, 93, 113,
  95, 112, 159, 13, 30, 28, 19, 34, 6, 45, 71, 19, 50, -63, -50, -68, 0, 16,
  0, 10, 20, 5, 4, -10, 16, 25, 17, 12, 51, -76, 41, 1, 38, -19, 17, -16, 6,
  6, 12, 33, 49, 27, -28, 3, 9, 32, 28, 11, -29, -19, 0, 17, 9, -12, -5, 36,
  -24, -2, -12, -14, -25, 34, -2, 41, 141, -3, -1, -19, 5, 19, 29, 9, 31,
  -24, 149, 2, -7, 1, -32, 7, -5, -2, 26, -9, 215, 9, -13, 5, -13, -13, -12,
  -20, -26, 3, -131, -74, -142, -50, -140, -116, -41, -17, 270, 4, 1, 7,
  -10, -9, 7, -25, -25, 13, 33, 0, -1, -25, 25, -14, -3, -1, 0, -13, 25,
  -14, 29, 0, 16, -4, 2, -12, -15, -7, -10, -8, -15, -10, 31, -22, -3, -8,
  -1, 2, -2, 12, -28, -32, -40, -32, 3, 18, -32, -59, -31]

theorem fractionalNearFrameSubtreeG2R0522_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0522Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0522Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0522Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0522_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0522LowerBoundTable : List ℤ :=
  [8, -107, -14, 1, 105, 71, 103, 0, 80, 10, -61, -44, 7, 47, 31, -16, 85,
  30, 67, -69, 82, 176, 166, 167, -38]

def fractionalNearFrameSubtreeG2R0522LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0522Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0522LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
