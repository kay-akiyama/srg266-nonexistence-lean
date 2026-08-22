import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0048`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0048Mask : ℕ := 961646570414482

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0048Witness : Array ℤ :=
  #[-7, 97, -41, -158, -31, -2, 31, 25, -28, 31, 4, -21, -1, -19, -29, 24,
  13, -13, 3, -71, 6, 38, -2, 36, -30, -3, 5, 40, 12, -25, 16, 11, 57, 25,
  -21, -38, 3, 25, 2, 20, 46, -22, -46, -86, 2, 39, 15, 107, 107, 108, -33,
  -79, -107, -119, -3, 133, -36, 1, 0, 8, 52, -70, -46, 35, 23, 34, -55, 25,
  29, 171, -14, 13, 130, -59, 32, 34, -24, 27, 40, -21, -43, 19, -21, -8,
  56, 62, 128, 143, 67, 20, 35, -33, 123, 18, -14, 45, -45, 6, 32, 21, 9,
  -35, 2, 35, -14, -20, 62, -35, -45, -37, -31, 16, 98, 18, -19, 5, -84,
  -61, 7, -9, -6, -3, 74, -75, -81, -58, -66, -25, 29, 40, -22, 4, 23, 0,
  -81, 61, -40, 11, 44, -10, 28, -42, -26, 19, 7, 54, 13, -74, 44, 29, -11,
  59, -55, -13, 8, 16, -9, 0, 0, 14, -23, 2, 74, -67, -62, 78, -87, 43]

theorem fractionalNearFrameSubtreeG3R0048_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0048Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0048Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0048Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0048_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0048LowerBoundTable : List ℤ :=
  [-25, -50, 141, -32, 85, 148, 8, 2, 46, 11, -60, 51, 10, 312, 376, -29, 9,
  193, 168, -271, 79, 200, 9, 67, 174]

def fractionalNearFrameSubtreeG3R0048LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0048Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0048LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
