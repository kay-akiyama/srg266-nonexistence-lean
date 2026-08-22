import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0054`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0054Mask : ℕ := 4949368280762885

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0054Witness : Array ℤ :=
  #[16, 0, 2, 30, -21, -4, 0, -7, -3, 53, -1, -6, -36, 0, 45, 20, 0, -19,
  31, -9, 37, 1, 1, -27, -3, -5, -33, 23, 0, -29, 0, -11, -5, -28, -8, -37,
  55, 13, -18, 35, 4, 27, 17, 46, 13, 19, 25, 36, -26, 26, -27, -3, -14, -7,
  -16, -24, -22, 47, -39, -22, 33, -2, 0, 39, -2, -8, -13, -15, -9, 15, -21,
  24, 23, 2, -16, 8, 16, -25, 17, -35, -25, 35, -10, 15, 21, -6, -13, -64,
  12, -38, 29, 0, 27, -12, 10, 34, -31, -11, 30, -20, -7, -9, -61, 54, -73,
  -20, 12, 1, 23, 33, -9, -27, 28, 34, -1, -16, -3, -23, 19, 7, 2, 11, -13,
  9, -9, -45, -17, 50, -9, 11, -20, 2, 18, 22, 10, 1, 8, 2, 7, -17, 3, 7,
  41, -33, -66, 7, 53, -21, 31, 30, -4, 32, 33, -13, -16, 6, -15, 35, 23,
  55, 20, -30, -13, 41, -23, -10, 12, -25]

theorem fractionalNearFrameSubtreeG5R0054_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0054Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0054Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0054Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0054_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0054LowerBoundTable : List ℤ :=
  [-11, 30, 0, -33, 31, 2, 79, -26, 3, 154, 134, 9, 97, 80, 10, 29, 2, 10,
  11, -2, 127, 82, -1, 9, 63]

def fractionalNearFrameSubtreeG5R0054LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0054Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0054LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
