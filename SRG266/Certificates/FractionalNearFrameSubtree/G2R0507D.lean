import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0507`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0507Mask : ℕ := 5811646298409640

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0507Witness : Array ℤ :=
  #[-81, -57, -95, 2, -21, 41, 137, 7, -31, 36, 95, -39, -33, 58, -11, -11,
  -46, -84, 63, 146, 85, 30, -47, -73, 49, -88, 40, -5, 122, 120, -87, 15,
  36, 19, -128, 36, 65, 18, 48, -8, 7, -78, -101, -78, -25, 50, -28, 29, 39,
  -44, 67, 109, 81, -118, 87, -29, -46, 11, -40, 2, 66, 192, 162, -9, 40,
  19, -25, 102, 4, 4, 71, -81, 16, 56, 40, -47, -51, -45, 18, 128, -90, -67,
  88, 124, -37, -89, -11, -60, -50, 35, -29, 60, -16, 29, -99, -6, 4, 40,
  67, 89, 54, -34, 53, 185, 47, -10, 78, -17, -36, -42, -96, 33, 91, 39, 35,
  -15, 83, 12, -99, -1, -99, -81, 89, 84, 29, 60, 53, 55, 82, 54, -26, -8,
  14, 106, 104, -4, 50, 117, 133, -49, 95, 44, 34, -27, 182, -76, -13, -146,
  -23, 136, 98, 80, 38, -27, 15, 39, -33, -104, 182, 22, 48, -18, 14, -86,
  68, -59, 78, 4]

theorem fractionalNearFrameSubtreeG2R0507_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0507Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0507Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0507Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0507_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0507LowerBoundTable : List ℤ :=
  [164, 316, 269, 206, -53, 120, 105, 330, 251, 448, 10, 456, 107, 267, 109,
  190, 575, 10, 11, 9, 91, -197, 166, 10, 474]

def fractionalNearFrameSubtreeG2R0507LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0507Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0507LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
