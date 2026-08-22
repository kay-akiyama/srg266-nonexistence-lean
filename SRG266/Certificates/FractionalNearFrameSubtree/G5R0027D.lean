import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0027`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0027Mask : ℕ := 1110010959463010

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0027Witness : Array ℤ :=
  #[-47, 63, 10, -19, -5, 75, -35, 5, -9, 21, -61, -1, 36, -23, 0, 0, -4,
  -45, 24, -1, 9, -49, -66, -17, 25, 0, -35, -37, 102, 24, 54, 42, -43, 54,
  108, 83, 138, -93, 59, 72, 9, -76, -83, -125, -33, -44, -138, -72, 13, 55,
  14, 69, 94, 90, 69, -18, 19, 94, 71, -7, 10, 8, -36, -6, -25, -30, -20, 3,
  11, -50, 67, 34, 59, 0, -4, -32, 28, -24, 54, -1, 88, -45, 21, 4, 105,
  -12, 10, -66, -61, 0, -51, 5, 61, 70, 42, -38, 31, -38, 20, 34, -25, 46,
  -69, -41, -27, 23, 60, -72, 31, 26, -57, 43, 52, 48, 57, 36, 6, -27, 16,
  -22, 0, 75, 57, 9, 30, 8, -29, 67, -24, 4, -11, 48, 53, -20, 68, 55, 37,
  22, -25, 26, 4, -61, -47, -4, 30, -21, -1, -21, -19, -15, 54, 60, -28,
  -40, 39, -1, 84, -52, 28, -48, 35, -40, -42, 65, 2, 50, -34, 49]

theorem fractionalNearFrameSubtreeG5R0027_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0027Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0027Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0027Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0027_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0027LowerBoundTable : List ℤ :=
  [34, 93, 72, 2, 89, 114, 93, 3, 155, 154, 176, 141, 175, 50, 372, -54, 82,
  99, 126, 88, -6, -149, 110, 362, 186]

def fractionalNearFrameSubtreeG5R0027LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0027Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0027LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
