import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0061`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0061Mask : ℕ := 4980124541569169

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0061Witness : Array ℤ :=
  #[31, -54, 31, -35, -86, 106, 0, 123, 127, 159, 67, -195, -67, 69, -93,
  -7, 56, -77, -34, -40, -81, 140, 46, -47, 32, -6, 57, 132, 20, -22, -14,
  27, -27, 0, 21, 37, 69, 82, -13, -4, -34, -92, -35, -55, -30, 18, -14, 72,
  -16, -1, 72, -30, -23, 26, 34, 60, -25, 51, 104, -37, -35, 30, 45, -130,
  -24, 70, 26, -3, -55, 32, 56, 38, -93, -9, -1, 16, -27, 0, -8, 10, 23, 9,
  -78, 1, 9, -156, -75, 45, 30, 18, 62, -83, 75, -17, -30, 67, 68, 67, 64,
  29, -68, 94, -66, 19, -110, -14, -124, 105, 98, 4, -11, -53, -69, 0, -25,
  -53, -33, 42, -32, -3, 71, 60, -57, 29, 0, -8, -3, 26, 0, 92, -8, 62, -32,
  100, -40, -35, -34, 62, -20, 141, -42, 63, 18, -14, 38, 4, -57, -5, 79,
  64, 32, -137, 81, 55, 112, -7, 16, -41, -42, -14, -27, 40, 82, 9, 2, -35,
  -23, 0]

theorem fractionalNearFrameSubtreeG5R0061_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0061Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0061Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0061Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0061_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0061LowerBoundTable : List ℤ :=
  [10, 122, -41, 35, 149, 43, 170, 56, 44, 254, 179, 225, 114, 301, -289,
  120, 112, -95, 10, -45, 29, 193, 161, -237, 417]

def fractionalNearFrameSubtreeG5R0061LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0061Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0061LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
