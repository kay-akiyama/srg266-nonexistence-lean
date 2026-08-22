import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0052`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0052Mask : ℕ := 963845702652578

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0052Witness : Array ℤ :=
  #[-45, -15, -4, -58, -17, -15, 69, 0, -16, 67, 7, -7, 7, -24, 14, 5, -37,
  12, -1, 3, -25, -11, 33, 40, -9, -5, 32, 25, 30, -41, -20, -41, 20, 37, 6,
  0, -35, 30, -5, 21, -39, -48, -119, -71, -120, 9, 29, 40, 97, 80, 17, 36,
  0, -102, -58, -31, 31, -20, -24, 0, 23, 9, -13, -89, 108, 5, -48, -34, -3,
  -19, 32, -76, 21, -37, -31, -59, 10, -7, 11, 86, 8, 17, -26, -14, -79,
  -61, -11, 32, 34, 50, -93, 69, 34, 76, -18, -27, 8, -18, 18, 50, -22, -7,
  -81, -19, -10, 20, -45, -68, 15, 83, 52, 44, 45, 115, 79, 45, 11, 9, -73,
  2, 6, 24, 58, 96, -25, -16, 82, -54, -45, -21, 6, 7, 5, 36, -12, 57, 34,
  -29, 2, 131, 23, -68, -111, 33, -13, -32, -8, 23, -8, -15, 60, 31, 20, 86,
  -43, 13, 14, -7, 23, 0, 3, 0, -52, 61, 17, 11, -25, 98]

theorem fractionalNearFrameSubtreeG3R0052_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0052Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0052Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0052Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0052_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0052LowerBoundTable : List ℤ :=
  [17, 184, -86, 3, 55, 77, -27, 7, 2, 204, -101, -13, 288, 10, 61, 93,
  -216, -9, 30, 10, -107, 26, 159, 112, 10]

def fractionalNearFrameSubtreeG3R0052LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0052Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0052LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
