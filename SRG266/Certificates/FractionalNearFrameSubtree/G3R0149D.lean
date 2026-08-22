import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0149`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0149Mask : ℕ := 6850200024779340

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0149Witness : Array ℤ :=
  #[28, 31, -65, -79, 65, -15, -33, -7, -23, -82, -30, 36, 11, -12, -7, 37,
  -12, -11, -12, -48, 86, -11, -19, -21, -75, -10, -20, -14, -31, -72, 17,
  -76, -40, 29, 22, 53, -55, -53, -23, 132, 114, 80, -48, -59, 33, 3, -57,
  -28, 55, 38, -10, -51, 1, 4, 109, 33, -54, -20, 61, 38, 34, 66, -62, 31,
  0, -21, 63, -2, -81, -26, 49, -35, 23, 46, 9, -26, 17, 80, 44, 60, 21, 54,
  -18, 41, -5, 8, 21, 6, 131, -24, 34, 51, -12, 28, 13, 2, 36, 65, -24, 29,
  24, 52, 98, -72, -73, -109, -55, -23, -98, 13, -47, -32, -21, 47, 27, 43,
  -28, -12, -12, -15, 16, 47, -69, -3, 15, 3, -37, -45, -13, -18, 26, -5, 2,
  22, -77, 11, 61, 5, -17, 44, -8, 30, -3, -12, -4, 0, -28, -8, -30, 1, 43,
  -21, 67, 26, 39, 32, -77, 62, 12, 8, 15, 19, 49, 1, 0, -40, 11, 80]

theorem fractionalNearFrameSubtreeG3R0149_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0149Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0149Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0149Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0149_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0149LowerBoundTable : List ℤ :=
  [-5, 20, 305, 97, -83, 2, 104, -53, -6, -16, -43, 8, 11, 8, 161, 87, -35,
  -77, 179, 32, 10, -16, 10, 195, 59]

def fractionalNearFrameSubtreeG3R0149LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0149Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0149LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
