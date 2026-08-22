import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0510`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0510Mask : ℕ := 5812252308591380

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0510Witness : Array ℤ :=
  #[47, 18, 26, -22, 30, -11, 22, -58, 11, 28, 67, -73, -30, -30, 0, 34, 9,
  -14, -48, 13, -20, -11, -2, 4, 6, 78, -1, 28, -45, 49, -35, -27, -3, 3,
  -46, -53, 31, -43, 98, 25, -10, 26, -9, -17, 65, -15, 42, -52, -57, -61,
  21, 55, 32, 21, -54, 3, 21, -27, -18, 118, 12, 12, -81, -16, -25, 99, 96,
  -71, -2, 21, 43, -27, 49, -1, -30, 89, 54, 22, 12, 30, 5, -19, -19, -12,
  -20, 45, 7, -22, 23, 34, -21, -11, 5, -3, 64, -17, 78, -22, 47, -12, -3,
  -12, -10, 7, -35, -24, 66, -18, -29, 49, -23, -40, -3, 32, 45, 26, 19,
  -12, 9, 31, 47, 14, 4, 43, -36, 40, -8, 51, 19, 54, 64, 5, -7, -5, 41, -5,
  23, 4, -6, 38, 9, 79, 43, 39, 3, -27, -48, 76, -9, -27, -77, -33, 27, -3,
  -41, 40, -20, 33, 17, -5, 26, 19, -8, -77, -17, -34, 14, -5]

theorem fractionalNearFrameSubtreeG2R0510_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0510Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0510Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0510Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0510_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0510LowerBoundTable : List ℤ :=
  [44, 84, 40, 159, 2, 78, -65, 48, 101, 273, 155, 44, 116, 19, 43, 112,
  285, 225, 10, 88, 115, 11, 162, -32, 134]

def fractionalNearFrameSubtreeG2R0510LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0510Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0510LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
