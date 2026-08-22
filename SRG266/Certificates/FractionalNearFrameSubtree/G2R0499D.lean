import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0499`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0499Mask : ℕ := 5811375933444760

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0499Witness : Array ℤ :=
  #[-8, -41, 41, -20, 19, -2, 0, -24, -14, -73, 22, 3, 56, -40, 30, -35,
  -25, 1, -37, -22, 35, -9, -22, 40, -41, -46, 35, -32, -9, 8, 9, -4, 54,
  -29, -10, -1, 45, 50, -104, 27, -20, -15, 36, 2, -60, -15, 38, 35, -23,
  28, -22, 77, 16, -6, 17, 32, 19, 23, -40, 12, -15, -9, -11, -37, 24, 0,
  11, -15, 38, 8, -63, 37, 27, -43, -30, 2, 8, -11, -12, -33, -41, 20, -27,
  4, -34, 29, 42, -6, 19, 26, -106, -2, 58, -12, 5, 21, 47, -7, 37, 52, -10,
  4, 4, 11, -43, -11, 15, 20, 31, 34, 26, 0, 28, -12, 5, 39, 63, -25, -54,
  -53, 43, 1, -44, 48, 44, 58, 15, -95, 3, 0, 38, 29, 29, -47, -35, 21, -56,
  0, 5, -37, 41, -44, 56, -6, 22, -3, 79, 26, -31, 4, 20, -4, -30, 41, 38,
  -11, -38, 55, -119, -13, -40, -2, 35, 49, 4, -58, -1, -49]

theorem fractionalNearFrameSubtreeG2R0499_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0499Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0499Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0499Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0499_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0499LowerBoundTable : List ℤ :=
  [-43, -8, 3, -66, 73, -41, 27, 121, -101, 6, 131, 131, -60, 242, -111, 7,
  -128, 5, 10, 97, -76, 124, 167, -103, 110]

def fractionalNearFrameSubtreeG2R0499LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0499Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0499LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
