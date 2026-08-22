import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0024`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0024Mask : ℕ := 1109710606139730

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0024Witness : Array ℤ :=
  #[90, -3, -79, 25, 10, -95, 95, 80, 70, 1, 187, -10, -93, -111, 118, -178,
  42, -72, 82, 0, 113, -19, 42, 12, 161, 9, -118, -25, -15, 12, 56, 63,
  -144, -9, -81, -152, -159, 93, -54, -137, -92, 162, 136, 141, 144, 4, -1,
  -34, 100, 15, 90, -98, -67, 74, 113, -65, -60, -3, 35, -122, -53, 23, 24,
  -58, -157, 23, 9, 84, -81, 42, 91, 24, 55, -97, 12, 62, 21, -36, 71, 98,
  17, 2, -43, 41, 30, 40, -66, -18, -87, -77, -5, 70, 11, 12, -76, 119, 82,
  18, -38, 70, 121, 105, 29, -10, 40, 19, 51, 2, 73, -30, -20, 96, -124,
  104, 0, 17, -81, -95, 0, 21, 33, -138, 13, 58, -36, -18, 9, 98, 102, 47,
  -31, -126, -68, -69, -62, 6, 162, -46, 139, -86, -103, -30, 41, -56, 70,
  94, -79, 4, -70, -105, -28, 83, -59, -10, -42, 78, 197, 93, 39, -159, 84,
  16, -5, 107, 109, -16, 98, 66]

theorem fractionalNearFrameSubtreeG5R0024_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0024Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0024Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0024Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0024_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0024LowerBoundTable : List ℤ :=
  [16, 82, 252, 95, 115, 1, 107, 50, -27, 243, 283, -47, 51, 207, 299, 10,
  451, 85, 60, -325, 190, 293, -141, 70, 194]

def fractionalNearFrameSubtreeG5R0024LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0024Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0024LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
