import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0146`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0146Mask : ℕ := 6848699243795106

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0146Witness : Array ℤ :=
  #[8, 10, -8, 60, -60, 67, 61, 35, -22, 0, 150, 9, -8, 2, -59, 105, -2, 50,
  64, -4, 11, 85, 30, 105, 32, 27, -36, -68, -119, -135, 34, -32, -4, -36,
  -24, -126, -75, 72, -5, 45, -40, 32, 59, 4, -17, 8, 36, -56, -56, -50,
  -24, 25, -1, -21, 73, 59, -158, 76, -29, 24, 69, 23, -111, 116, -48, 7,
  -53, -132, 30, -78, 17, 63, 49, 40, -22, -1, -72, -88, 0, 0, 8, -61, -14,
  -9, 41, -56, 63, 104, 21, 23, 72, 33, 73, -73, -19, 45, 10, 31, -83, 29,
  -48, -44, -46, 48, 120, 101, -51, 74, 10, 29, -68, -51, -13, -44, -9, -83,
  -48, -39, 39, 114, 30, -23, 23, 92, 28, -27, 135, -26, 1, 12, -16, 4, 46,
  94, 96, 15, -20, -35, 24, 30, 33, -113, 13, -31, 34, -6, 60, -74, 47, -45,
  0, -36, 31, 79, 35, 35, 95, -14, -56, 25, 69, -149, 53, 43, -180, -28, 65,
  12]

theorem fractionalNearFrameSubtreeG3R0146_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0146Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0146Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0146Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0146_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0146LowerBoundTable : List ℤ :=
  [-30, 81, 2, 89, 1, 128, 2, -4, -58, 211, -5, 289, 11, -34, 148, 252, 73,
  -43, 310, 455, 11, 126, -152, 33, 7]

def fractionalNearFrameSubtreeG3R0146LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0146Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0146LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
