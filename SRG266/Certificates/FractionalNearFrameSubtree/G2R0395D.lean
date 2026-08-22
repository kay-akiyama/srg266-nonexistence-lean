import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0395`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0395Mask : ℕ := 5740359780508066

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0395Witness : Array ℤ :=
  #[-29, 66, 59, -122, 52, -134, 79, -126, 0, -21, -131, 43, 51, 49, 97, 81,
  50, 55, -78, 22, 1, 65, -9, -37, 43, -83, -11, 13, 0, -8, -86, 27, -32,
  28, 45, -63, 59, 43, 13, 48, -54, 38, 15, 22, 27, 90, 95, 105, -69, -49,
  -67, -78, -64, -41, -84, -46, -28, -24, 9, 38, -36, 48, 87, 2, -2, -23,
  46, 22, 24, -66, 35, -23, -61, 51, -9, 43, -6, -15, -31, 3, 149, 24, 41,
  -121, 139, -5, 19, 22, 8, 10, -51, -22, 6, -24, 6, -12, -56, 12, 31, 41,
  63, 10, -98, 63, 141, 61, -64, -16, 28, -77, -76, 90, -83, -143, -12, -34,
  -53, 0, 11, -53, -20, -9, -6, 35, -13, -33, -12, -19, -29, -19, 11, 90,
  -88, 11, -30, 46, 32, 32, -29, 40, -9, 52, -95, -120, 63, 11, 3, 6, -11,
  24, 75, 25, 15, 8, -5, -29, 48, -16, -5, -12, -13, 6, -29, -13, 2, -8,
  -88, -31]

theorem fractionalNearFrameSubtreeG2R0395_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0395Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0395Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0395Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0395_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0395LowerBoundTable : List ℤ :=
  [-84, -89, -138, -9, 3, 24, 55, 50, 24, 11, 227, -374, 9, -242, 384, 45,
  -128, -172, 14, 223, 28, 267, 107, -209, 89]

def fractionalNearFrameSubtreeG2R0395LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0395Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0395LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
