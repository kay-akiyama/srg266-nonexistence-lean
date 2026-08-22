import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0144`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0144Mask : ℕ := 6848293834755594

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0144Witness : Array ℤ :=
  #[-54, 36, 9, -26, -15, -14, -9, -49, 0, -59, -56, 100, 108, -19, 25, -9,
  46, 24, -1, 8, 118, -39, 8, -35, 94, -24, -29, 3, -39, -103, -65, 16, -9,
  52, -159, -25, -10, 24, 72, 83, 28, 39, 7, -38, 24, 51, 76, 9, -33, 105,
  -64, 7, 38, 0, 11, -49, 39, 12, 52, -47, 70, -42, -39, -40, 77, 24, -5,
  10, -7, 35, 33, -11, -3, 2, 48, -48, 20, -1, 33, 83, -61, -31, 28, 5, 53,
  0, 0, -90, 70, -1, -8, -23, 74, -7, -22, 45, -41, -104, 81, -39, 27, 4,
  34, -24, -61, -126, -37, 109, 74, 55, -23, 22, -34, -65, -77, -66, 49,
  -17, 65, 27, 75, 101, -75, 32, -37, 24, -32, -39, 132, 50, -15, 18, -14,
  -95, 36, 170, -32, -126, -21, 7, -49, -85, 65, 16, 10, -43, -44, 20, 24,
  110, -47, 55, -12, -51, -6, -52, 91, 73, 3, -14, -20, 28, -30, 25, -59,
  -38, -22, 81]

theorem fractionalNearFrameSubtreeG3R0144_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0144Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0144Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0144Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0144_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0144LowerBoundTable : List ℤ :=
  [-22, 23, 46, 112, 119, 43, -98, 2, -42, -40, 28, -170, 3, 230, 7, 106,
  12, 340, -12, 117, 10, 376, 12, -5, 266]

def fractionalNearFrameSubtreeG3R0144LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0144Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0144LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
