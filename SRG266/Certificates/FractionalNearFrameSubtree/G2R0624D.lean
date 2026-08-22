import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0624`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0624Mask : ℕ := 9749079312024850

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0624Witness : Array ℤ :=
  #[-35, -99, 62, -16, 54, -63, 25, 128, 145, 117, 8, -66, -123, -49, 4,
  -139, -98, -171, -25, 37, -8, -104, -64, -30, -4, -5, 96, 51, 133, 130,
  99, -9, 27, 13, -123, 33, -114, -38, -25, -21, -64, -31, 42, 59, -51, -52,
  -73, 47, -87, 44, -5, 3, 55, 57, -25, 124, 69, 33, -41, 48, -113, -110,
  99, 7, -75, 72, -71, -27, -105, 42, 32, -63, -17, -79, -152, 76, 39, -145,
  85, 25, 40, -121, -61, 67, -21, -98, 42, 58, 56, -22, -47, 45, -83, 9,
  -172, -88, 65, -12, -37, 89, 15, 14, -45, 35, 67, 11, 85, 21, 21, 37, 0,
  20, -95, 6, -10, 33, 90, 122, 52, 49, 10, 113, 106, -8, -20, 6, 46, 58,
  40, -1, -27, 37, 40, -109, 33, 9, -25, -100, 14, -58, -2, -5, 15, 36, 53,
  -4, 74, 67, 61, 38, 70, -24, -69, 9, 77, 112, -32, -6, 121, -6, -6, 71,
  -39, 55, 69, -3, -179, 0]

theorem fractionalNearFrameSubtreeG2R0624_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0624Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0624Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0624Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0624_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0624LowerBoundTable : List ℤ :=
  [-32, 228, 61, 44, -98, -98, -10, 66, -100, 401, 299, 22, 252, -110, 143,
  91, 168, 194, -248, 291, 231, -270, -264, 40, -114]

def fractionalNearFrameSubtreeG2R0624LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0624Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0624LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
