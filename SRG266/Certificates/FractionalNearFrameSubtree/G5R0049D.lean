import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0049`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0049Mask : ℕ := 4877219205427461

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0049Witness : Array ℤ :=
  #[28, 38, -1, 43, 51, -48, 58, 76, -71, 53, 71, -125, 0, -55, -145, -33,
  -2, 0, 41, 25, -66, -23, 6, -29, -81, -89, 3, -5, -88, 83, 70, 98, -1, 39,
  19, -34, 1, -40, -80, 23, 19, -11, 34, -28, -44, -34, -69, -94, 54, 27,
  140, 27, 12, 90, 142, -80, -49, 63, -72, -60, 58, -29, 13, 45, 53, 30, 79,
  -33, 59, -16, 45, -25, -101, -32, 7, -38, 61, 91, 55, 28, -85, -18, 6, 69,
  58, -22, 1, -6, 118, -6, -20, -33, 32, -89, -5, -66, -32, 32, -25, 107,
  51, -31, 90, 159, 45, -25, -8, -38, -3, 23, 28, -42, 30, -18, 21, 98, -12,
  -59, -39, -7, -51, -33, 47, -3, 70, 75, -88, -1, -93, -4, 57, 131, 11, 17,
  77, -14, 36, -25, 141, 85, 44, 75, -55, -27, -102, 61, -52, 30, 64, -33,
  -57, 42, 63, 5, 65, 85, -113, -98, -116, -87, -1, 17, 0, -57, -79, -98,
  -33, 78]

theorem fractionalNearFrameSubtreeG5R0049_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0049Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0049Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0049Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0049_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0049LowerBoundTable : List ℤ :=
  [-35, 1, 17, 74, -27, 58, 14, -44, 2, 389, 10, -197, 68, 10, 238, 92, 238,
  126, 161, 125, 9, -100, 258, 444, -147]

def fractionalNearFrameSubtreeG5R0049LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0049Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0049LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
