import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0036`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0036Mask : ℕ := 954156147673490

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0036Witness : Array ℤ :=
  #[41, 87, 0, 26, 10, 92, 7, -14, -61, -34, 53, 9, 13, -50, -59, -48, 18,
  -38, 3, 78, -94, 13, 89, -44, -55, 1, 64, 31, 93, 17, 88, 5, 23, 31, 22,
  -28, 10, 15, -44, 8, 0, -51, 92, 26, 27, -26, -116, 25, 53, -16, -40, -60,
  18, -122, 109, 68, 74, -26, -10, 26, 39, -7, 4, 63, -22, -32, -36, -14,
  115, 48, -51, 40, 3, 87, -23, -61, -30, 48, -76, -36, -30, 6, -42, -99,
  18, 19, 21, 21, 10, -36, 18, 29, 52, 30, 37, 30, 10, 6, 49, -2, 73, -18,
  22, 47, -37, 8, 50, -5, -68, -23, -30, 63, 67, -42, -3, -38, -54, -35, 19,
  -12, -19, 35, 56, -43, -56, -28, 27, 21, 45, 25, 37, 11, 57, 85, 2, -10,
  -5, 38, 59, 131, 39, 17, 20, 33, 54, 42, 11, -91, 115, 12, 104, -28, 13,
  12, -21, -15, 41, 13, -59, -12, 0, 61, -48, 26, 27, 18, -7, -35]

theorem fractionalNearFrameSubtreeG3R0036_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0036Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0036Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0036Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0036_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0036LowerBoundTable : List ℤ :=
  [48, 173, 91, 134, 82, -45, 153, -17, 147, 10, 360, 107, 119, 188, 15, 10,
  293, 98, 220, 4, 59, -97, 411, 216, 195]

def fractionalNearFrameSubtreeG3R0036LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0036Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0036LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
