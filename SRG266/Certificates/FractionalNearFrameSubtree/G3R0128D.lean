import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0128`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0128Mask : ℕ := 5402573011071656

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0128Witness : Array ℤ :=
  #[-4, -34, 2, 32, -18, -3, -11, -21, 9, -26, 25, -14, 41, -5, 40, -8, 4,
  43, 20, 37, 13, -45, -10, 4, 33, 7, -5, -18, -18, -36, -66, 26, -11, -56,
  -76, 16, 54, 49, 15, 7, 49, -13, -15, 57, -67, -62, 42, 6, 43, 15, 49,
  -78, 5, 40, -21, 0, -13, -9, -7, -14, 1, -73, -17, -21, 0, -47, 82, -99,
  -5, -24, 60, -78, 30, 100, -119, -11, -10, -12, -47, -26, -3, 16, 31, 36,
  16, -37, -46, 4, -1, -16, 34, -12, 95, 31, 19, -20, -24, 50, 24, 81, 64,
  63, -60, 20, 19, 5, 13, -30, -21, -57, -111, -14, 9, -9, -13, -42, -23,
  -90, 69, -10, 78, 5, 27, 45, 0, 97, 40, 24, -17, 32, 7, -43, -49, 30, 111,
  -13, 21, -23, 47, 83, -33, 51, -89, 36, 12, -4, 22, -4, 62, 56, -29, 4,
  17, -97, 49, -60, -120, -55, 20, 18, 81, -40, -44, 49, 44, -39, -132, 90]

theorem fractionalNearFrameSubtreeG3R0128_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0128Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0128Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0128Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0128_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0128LowerBoundTable : List ℤ :=
  [-42, 49, 3, 56, -42, 2, -22, 46, -50, -127, 35, 256, 84, 2, -5, 136, -25,
  58, 153, 10, -69, -50, -24, 153, -29]

def fractionalNearFrameSubtreeG3R0128LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0128Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0128LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
