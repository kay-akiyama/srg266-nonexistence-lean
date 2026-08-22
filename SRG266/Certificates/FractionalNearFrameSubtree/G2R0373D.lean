import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0373`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0373Mask : ℕ := 5737061396714122

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0373Witness : Array ℤ :=
  #[-153, -197, -50, 33, -44, -177, 225, 217, 207, 219, 62, -182, -122, -5,
  -38, 109, -157, -110, 2, 29, -71, -61, -14, 7, -24, 15, 54, 132, 125, 149,
  67, -81, -57, -198, -12, 21, 107, -7, -23, 72, 75, 251, -18, -26, -87,
  -112, 39, 49, 151, 80, 2, 28, 227, 182, 86, 182, -30, -156, 90, 105, -109,
  32, -27, 131, -68, -114, -35, 1, -3, 58, 19, 11, -57, 79, 83, -83, 51,
  -108, -13, -27, -107, 9, -2, -25, 35, -88, 88, 77, 20, 9, 69, 15, 9, -10,
  81, 64, 61, 46, 123, 43, 199, 72, -54, -96, 62, 122, 117, 70, 22, 50, 33,
  62, 80, 32, 56, -152, 113, 14, 0, 38, -6, -29, -90, 5, -60, 61, 62, 37,
  163, -121, -36, -37, 12, 74, 3, 39, -9, 73, -134, 27, -88, -147, 76, -84,
  -133, -82, 57, -85, 49, 144, -41, 182, -30, 73, 246, 93, 24, 130, 91, 113,
  -6, 127, 9, 55, 40, -93, -83, -66]

theorem fractionalNearFrameSubtreeG2R0373_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0373Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0373Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0373Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0373_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0373LowerBoundTable : List ℤ :=
  [142, 76, 305, 240, 3, 252, 141, 144, 1, 745, 242, 248, 366, 310, 8, 297,
  458, 363, 359, 569, 181, 493, 67, 10, 499]

def fractionalNearFrameSubtreeG2R0373LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0373Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0373LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
