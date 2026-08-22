import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0113`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0113Mask : ℕ := 5793775441872969

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0113Witness : Array ℤ :=
  #[-18, -94, -121, -22, -70, 63, 28, 41, 146, 20, 56, 100, 49, -23, 8, -8,
  -33, 0, -68, -76, -30, 127, 44, 43, 45, 54, -3, 29, 63, 0, 20, 62, 18, -1,
  -47, 37, 67, 20, 52, -29, 24, 57, 61, 0, 2, -102, 25, 63, 105, 53, 37, -7,
  -5, -107, -109, -49, -43, 204, -47, 27, -19, 22, -93, 80, -95, 26, 102,
  89, -71, 4, 59, -44, 87, -35, 54, 40, 0, -65, 35, 44, 68, 38, -25, 5, 87,
  95, -46, 47, 3, -46, 11, 20, -50, 4, 91, -91, 37, -43, -146, -68, -87, 85,
  -45, 29, 81, -89, 181, 3, 48, -18, 106, -2, -86, -52, -24, 59, 5, -14,
  -22, 124, 99, 94, -121, -47, 39, -44, -92, 63, 110, -25, -79, 102, 153,
  37, 5, -13, -52, -66, 56, -31, -180, 72, 99, 51, 59, 18, 124, 30, 113, 51,
  1, 85, 0, -31, -113, -31, 57, -62, -30, 59, -59, -49, -4, -70, -19, -41,
  88, 39]

theorem fractionalNearFrameSubtreeG5R0113_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0113Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0113Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0113Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0113_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0113LowerBoundTable : List ℤ :=
  [11, 41, 2, 99, 113, 196, -57, 167, 113, 423, 334, 306, 114, 652, 224,
  221, 82, 126, -237, 273, -73, 88, 508, 319, -177]

def fractionalNearFrameSubtreeG5R0113LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0113Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0113LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
