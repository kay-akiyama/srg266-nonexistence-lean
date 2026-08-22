import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0055`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0055Mask : ℕ := 4949374907560965

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0055Witness : Array ℤ :=
  #[-14, -22, 27, 14, -36, -78, -30, -9, -26, -84, -87, 77, 83, 99, 92, 89,
  47, 52, 56, 49, 22, -10, -6, 16, 27, -51, -39, -8, -49, -59, -91, -39, 50,
  49, -19, -3, 5, 19, 2, 22, 17, -16, -7, -62, 17, 9, -1, 21, -58, -53, -61,
  -19, 5, -53, -41, 7, 69, 45, 19, 41, -3, -37, -46, -46, -81, -25, 11, 58,
  -8, -36, -3, -11, 14, 52, -13, -26, -32, -39, -7, -9, -8, -45, 9, 33, 21,
  -5, -34, -47, -15, -29, 23, -16, -17, -19, 2, -6, -45, -15, -2, 27, 6, 37,
  38, -2, 9, 18, -60, -49, 29, 12, 33, 26, 20, 47, 33, -8, 4, 32, 34, 43,
  -2, 9, 88, -1, 8, -70, -79, 61, 7, 34, 62, -29, -20, 23, -4, -24, 16, -12,
  31, 19, -18, 12, -13, 43, 45, 53, 36, 36, 5, 32, 38, 43, -21, -25, 0, 11,
  3, -6, 30, 16, -6, 2, -61, -13, -42, -43, -35, -23]

theorem fractionalNearFrameSubtreeG5R0055_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0055Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0055Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0055Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0055_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0055LowerBoundTable : List ℤ :=
  [-51, 56, -18, -59, 17, -46, 3, -52, 58, 103, 134, 10, 166, 125, -33, 80,
  139, -26, -58, 9, 12, 9, -29, -61, 87]

def fractionalNearFrameSubtreeG5R0055LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0055Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0055LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
