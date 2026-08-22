import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0006`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0006Mask : ℕ := 267864631595525

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0006Witness : Array ℤ :=
  #[-70, 7, 17, 31, -81, 0, 45, 22, 134, 0, 10, 79, -62, -23, -103, -32,
  -40, -19, -9, -58, 2, -90, -70, 67, -66, -130, -76, -14, 15, 87, 89, 62,
  9, 74, 6, 77, -68, 6, 30, 19, -4, 12, 23, 12, -56, 88, -108, 14, -2, 8,
  17, 7, 24, 42, 47, 49, 40, -24, 8, -12, 51, 17, 45, -2, -17, -87, 42, -66,
  -47, 59, 0, -64, 25, 9, 30, -5, 16, -16, -30, 133, 35, 7, 10, 2, -11, -40,
  -23, -17, -25, -29, 37, -9, 47, -32, 23, 22, 12, 5, 25, -18, 20, 72, 41,
  0, -32, 9, 31, -54, 1, -23, -54, -41, -33, -38, -1, -17, -1, 57, 1, -65,
  -47, -8, 82, 65, 56, -14, -71, -98, 19, 72, 16, 58, 5, -27, -46, 45, -13,
  -45, 0, 41, -35, -4, 66, -3, 29, 20, -14, 8, -7, 92, 11, 42, -46, 26, -83,
  8, 32, -5, -98, -19, 40, 9, -63, 27, 26, -23, 36, -20]

theorem fractionalNearFrameSubtreeG3R0006_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0006Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0006Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0006Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0006_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0006LowerBoundTable : List ℤ :=
  [-66, -4, 3, -29, 3, 3, 72, 87, 3, 317, -82, 5, 11, -8, -20, 98, 1, 80,
  -112, 10, -19, -19, 124, 188, 10]

def fractionalNearFrameSubtreeG3R0006LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0006Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0006LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
