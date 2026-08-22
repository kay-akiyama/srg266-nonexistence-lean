import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0051`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0051Mask : ℕ := 555008029536688

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0051Witness : Array ℤ :=
  #[133, 93, -24, -40, -56, 75, 124, 78, 60, 72, -17, 10, 72, -133, 119,
  -43, -21, 75, 3, -43, -24, 137, -92, -18, 96, 91, 82, 26, 0, 78, 7, 107,
  -96, 68, 27, 25, -77, -32, 18, -7, -27, -109, -66, -168, 107, 1, -24, 97,
  62, 59, -46, -60, -10, 66, -119, -53, -79, -102, 128, -19, 72, -132, -111,
  106, 187, -56, 85, -21, -2, -26, 5, 17, -74, -28, -26, 23, -97, 98, 90,
  97, 51, -5, 42, 84, 109, -48, -139, 123, -29, 42, 150, 48, 63, 107, 108,
  51, 67, -26, 32, 128, 86, 102, 41, 69, 45, -52, -31, 6, -45, 0, -32, -47,
  -155, -107, -28, 96, 109, 94, 63, -37, 20, 18, -60, -148, -96, 38, 53,
  -115, 54, 14, 108, 53, -81, -73, -101, -1, -2, 66, -51, -183, -45, 126,
  42, 37, 92, -70, 95, 20, 67, -56, -16, -49, 29, 19, 38, 83, -146, -155, 8,
  -29, -154, 9, 30, -37, 24, 30, 15, 12]

theorem fractionalNearFrameSubtreeG1R0051_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0051Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0051Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0051Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0051_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0051LowerBoundTable : List ℤ :=
  [-14, -91, 1, 1, 377, 1, 340, 3, 90, 207, 10, -193, 19, 201, 261, 34,
  -164, 577, 204, -12, 176, 383, 220, 328, 219]

def fractionalNearFrameSubtreeG1R0051LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0051Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0051LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
