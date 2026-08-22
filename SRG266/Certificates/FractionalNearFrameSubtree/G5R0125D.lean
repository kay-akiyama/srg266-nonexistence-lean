import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0125`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0125Mask : ℕ := 5861277728935186

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0125Witness : Array ℤ :=
  #[42, -49, -4, -69, -147, -97, 162, 116, -81, 120, -9, 69, -58, 46, 65,
  20, 0, -2, 8, -24, -54, -12, 140, 49, -194, -47, 109, 0, -72, 85, 40, 11,
  30, 78, -137, 20, -36, 96, -69, 15, -9, -134, 14, 13, -81, 43, -110, -49,
  51, 199, -29, 0, -58, 162, 76, 16, -64, -122, -107, -55, -17, -59, 156,
  51, 109, -3, -129, 32, 3, 133, 16, 56, -44, 10, 26, -63, 35, -84, -122,
  18, 19, 20, 17, 159, 121, 97, 13, 50, 68, 40, -123, 104, 85, -58, -26, 68,
  32, -10, 37, -90, -100, 74, -40, 19, 56, -191, 48, -13, 120, -57, -22,
  120, 109, 186, 122, 160, 62, 0, -132, -107, 62, 39, 43, -113, 120, 8, 86,
  -97, -73, -59, -115, -146, -87, -36, -7, 64, -24, 115, 42, 182, 180, 76,
  95, 123, 147, -9, -71, -134, 19, -24, -79, 123, -82, 17, -21, -58, -50,
  -114, 1, 119, 46, 24, -140, 71, 18, -119, 52, -228]

theorem fractionalNearFrameSubtreeG5R0125_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0125Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0125Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0125Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0125_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0125LowerBoundTable : List ℤ :=
  [-29, 30, 1, 2, -49, 171, -92, 80, 91, 75, 313, -3, 99, 254, -233, 84,
  188, 10, -156, 282, 396, 165, -29, 783, 567]

def fractionalNearFrameSubtreeG5R0125LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0125Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0125LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
