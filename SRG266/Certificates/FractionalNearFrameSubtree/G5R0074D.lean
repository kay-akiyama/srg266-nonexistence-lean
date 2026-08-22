import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0074`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0074Mask : ℕ := 5331106965209874

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0074Witness : Array ℤ :=
  #[6, 8, -24, 2, -8, 3, 111, -3, 0, -1, -14, -28, 8, -19, 7, 24, 4, -36,
  -9, -38, -18, 6, 78, 10, -10, -9, 5, 3, 24, 15, -6, 4, 62, -5, -24, -11,
  9, 18, 13, 17, -57, 16, -16, -3, 27, -2, 8, -22, 5, -28, 0, -10, 27, 16,
  -10, -39, 41, -27, -59, 12, -21, 54, 4, 12, -10, 9, 3, 5, 20, 39, -13, 26,
  -41, 30, 60, 17, -5, -29, -38, 19, -12, -27, 27, 51, 21, -17, -25, 19,
  -54, -75, 76, -20, -7, -21, 19, 30, 0, -11, 44, 15, 10, 14, 9, -28, -4,
  -11, -8, -17, -1, -4, 2, 4, 54, 127, 3, 0, -73, -81, -70, -17, 8, -14, 29,
  -27, -11, 13, 16, 5, 12, 0, 10, 52, 10, -84, -32, -19, 19, 44, 28, 11, 5,
  15, -28, -7, -79, -14, -7, 33, 55, 14, -15, -3, -4, 74, 16, 0, -15, -47,
  -15, -5, -7, 29, 21, -3, 17, -24, 18, 4]

theorem fractionalNearFrameSubtreeG5R0074_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0074Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0074Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0074Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0074_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0074LowerBoundTable : List ℤ :=
  [-12, 2, 1, 1, -16, 93, -7, 50, 39, 84, -35, 39, 62, 57, 91, 195, -131,
  -112, 11, 26, -8, 63, -19, -1, 134]

def fractionalNearFrameSubtreeG5R0074LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0074Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0074LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
