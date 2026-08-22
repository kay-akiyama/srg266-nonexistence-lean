import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0172`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0172Mask : ℕ := 6863001484203154

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0172Witness : Array ℤ :=
  #[-23, -53, 130, -53, 71, 75, -33, 35, 35, 56, 28, 20, -11, -43, 10, -43,
  -91, -88, -8, -113, 19, -42, 51, 112, 9, 91, 54, -9, 74, 71, -7, -49, 30,
  -4, 105, -36, -56, -2, 42, 55, -55, 22, 14, 75, -40, -5, 117, -30, -27,
  64, 13, -15, 34, 20, 104, -44, 162, 4, 39, 39, -27, -11, 30, -50, -63,
  118, -167, 9, -46, -110, -27, -59, 6, -76, -24, -87, -70, -25, 5, -79, 46,
  61, 80, 29, -23, 53, 52, 189, -98, 97, 80, -44, -6, -26, -15, 20, -9, 94,
  -16, 28, -29, 8, -47, 52, -65, 62, -145, -122, -128, -24, -41, -2, -37,
  24, 97, 6, 22, 22, 59, 16, 41, 107, 41, -116, -89, -21, 6, 56, -26, 29, 0,
  31, -23, 2, 10, 74, -14, -41, 60, -46, -19, 14, -32, 25, -44, 58, -5, -26,
  -80, 51, -31, 111, -102, 57, 48, -14, -9, -11, -3, -68, 56, 61, 16, 21,
  -39, 15, -3, 55]

theorem fractionalNearFrameSubtreeG3R0172_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0172Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0172Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0172Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0172_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0172LowerBoundTable : List ℤ :=
  [4, -33, 2, 190, -120, 261, 2, -47, 112, 318, 50, -195, 92, -7, 8, 178,
  -35, 18, 226, -76, 253, 209, 11, 10, 0]

def fractionalNearFrameSubtreeG3R0172LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0172Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0172LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
