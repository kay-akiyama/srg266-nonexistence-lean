import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0086`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0086Mask : ℕ := 2487830970141346

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0086Witness : Array ℤ :=
  #[24, 88, 30, 22, 62, 68, 8, 0, 0, 23, 66, -87, 11, -79, -28, -27, 27, 54,
  53, -114, -119, 44, 42, -3, -67, -37, 82, -16, 142, 8, 9, 99, 24, -18, 17,
  -53, 22, 18, -50, -73, -54, 5, 80, 39, 74, -57, 34, 40, -59, -123, -62,
  -182, -2, 79, 34, 122, 67, 8, -31, -91, -28, -63, 36, -66, -13, 31, 21, 4,
  -1, -46, 56, 41, 23, -34, 116, -3, 22, 37, 8, 6, 121, -97, 26, 36, 68, 28,
  -17, -55, -11, -94, 34, 9, -76, 37, -84, -56, 46, -51, 100, 57, -4, -6,
  -9, 31, 4, 7, 33, -46, 26, -14, -13, -25, 1, -33, -30, -26, 9, -62, 36,
  -16, -57, 108, 7, 35, 48, 26, -5, 12, -1, 82, -22, 16, 59, 40, -3, 6, 7,
  81, -8, 52, -78, 1, 52, -3, 7, -32, 87, 43, 9, -54, 45, -41, 61, 85, -36,
  -82, -53, 44, 21, -113, -60, 31, 20, 49, -81, 87, 50, 15]

theorem fractionalNearFrameSubtreeG3R0086_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0086Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0086Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0086Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0086_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0086LowerBoundTable : List ℤ :=
  [5, 89, 48, 2, -106, 32, 114, 100, 18, 125, 9, 216, 9, 9, 140, 213, -51,
  110, 107, 122, 41, 97, 159, 268, 83]

def fractionalNearFrameSubtreeG3R0086LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0086Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0086LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
