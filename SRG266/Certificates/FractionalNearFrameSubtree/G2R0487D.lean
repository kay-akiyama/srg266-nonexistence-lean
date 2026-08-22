import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0487`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0487Mask : ℕ := 5811145429926476

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0487Witness : Array ℤ :=
  #[32, 15, 19, 8, 1, 21, 79, 48, -19, 56, -26, 8, 15, 11, -26, -79, 1, 79,
  -40, -22, -37, 59, 68, -10, -68, 43, 79, 54, -73, 80, 20, 24, 17, -2, -1,
  5, -20, 70, -39, 27, 0, 29, -22, -1, 21, 21, 4, 60, -23, -58, -23, 41, 24,
  -16, -84, -36, 8, 1, -21, -16, 50, -47, 56, 26, 8, -14, 64, -1, 29, -11,
  -5, 22, 47, -11, 18, -18, -19, 34, 32, -2, 10, 23, -29, -5, 5, 1, -85, 37,
  41, 8, -69, -2, 76, 20, -4, -17, 45, 17, 13, 14, 47, -68, 4, 17, -21, 45,
  -55, 35, 16, -2, -13, -22, -3, -39, -50, -19, -44, -15, 77, -36, -74, -27,
  -87, 44, 16, 29, 45, 71, -37, -13, -6, -30, 32, 15, 50, 23, -89, 51, 34,
  55, 9, 6, 1, 18, -62, 13, 14, 45, 15, 65, 29, 45, -49, -66, -2, 23, 95,
  -2, -9, -22, -12, -3, -43, -48, 19, -61, 88, 60]

theorem fractionalNearFrameSubtreeG2R0487_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0487Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0487Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0487Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0487_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0487LowerBoundTable : List ℤ :=
  [11, 2, 66, 47, 47, 69, 110, 38, 153, -20, 106, 178, 69, 19, 10, -7, 123,
  -58, 3, 148, 135, 142, 209, 130, 10]

def fractionalNearFrameSubtreeG2R0487LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0487Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0487LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
