import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0125`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0125Mask : ℕ := 970127660663124

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0125Witness : Array ℤ :=
  #[42, -12, -11, -53, -72, -5, 126, 108, -15, -95, -79, 4, 97, -17, 114,
  108, 45, -37, 52, -83, 53, -33, -52, -60, 99, -51, 28, -54, -53, 115, 40,
  75, -12, 19, -4, 27, 37, -52, 89, -88, 78, -11, -7, 8, -59, 49, -43, 31,
  -14, 39, 50, 24, -86, 11, -32, 16, 70, -56, 113, -66, -5, 111, 141, -67,
  57, -30, 4, 71, -25, -53, -8, 61, 4, 32, -3, -103, 42, 8, 38, -41, -36,
  -62, 42, 102, -134, 49, -156, 24, 34, -25, 84, -12, 13, 3, 113, -42, 1,
  129, 50, 120, 80, -76, 48, 88, -36, 81, -38, -79, 51, -6, 45, 22, -35, 69,
  147, -5, -24, 67, 50, 90, -98, -19, 45, 46, 0, -94, 36, -10, -3, -45, 108,
  -17, 78, 92, -10, 42, -46, -12, -48, 28, -19, -72, -56, -5, 43, 14, 93,
  61, -35, -28, 27, -92, 66, 95, 71, -4, -18, 3, 35, 63, 22, -123, -71, -60,
  21, 58, -139, 26]

theorem fractionalNearFrameSubtreeG1R0125_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0125Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0125Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0125Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0125_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0125LowerBoundTable : List ℤ :=
  [29, -25, 75, 68, -77, 282, 257, 1, 7, 134, 244, 136, 135, 222, 596, 10,
  -117, 276, 100, 9, 182, 256, 338, 12, 552]

def fractionalNearFrameSubtreeG1R0125LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0125Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0125LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
