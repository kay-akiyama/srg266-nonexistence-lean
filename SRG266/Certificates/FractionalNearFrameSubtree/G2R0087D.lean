import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0087`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0087Mask : ℕ := 1213624515233865

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0087Witness : Array ℤ :=
  #[-60, -120, -85, -207, -33, -111, 106, -7, 71, -43, -56, 16, 69, 91, -17,
  -52, -1, 174, 46, -41, -57, -25, -35, 71, -73, 36, -50, 16, -24, 99, 11,
  105, -65, -120, -215, -78, -188, 144, 39, 0, -2, 30, 18, 5, 326, 81, 0,
  -93, 2, -41, 21, 72, 88, -18, 0, 76, 91, -10, -60, -118, 30, -23, 122,
  -51, 74, 114, 30, -86, -95, -68, -86, 16, 40, 123, 116, 76, -52, 37, 30,
  -44, -25, 46, 129, 89, 64, 52, 92, 29, 76, 86, 117, 108, 154, -57, 54, 3,
  20, 70, 29, 64, 15, 134, 10, -24, 70, 10, -5, 77, 115, -23, 16, 0, -73,
  -201, -150, -34, -127, -145, 110, 179, -77, -8, 7, 132, 48, -41, -29, 66,
  38, -131, 87, -24, 131, 82, -59, 6, 66, 79, -47, -22, -136, 93, -78, 5,
  24, -220, 95, -2, -91, 7, 26, -86, 58, 36, -60, 26, -10, -21, -53, 125,
  89, 4, -1, 182, -105, 48, -42, 29]

theorem fractionalNearFrameSubtreeG2R0087_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0087Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0087Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0087Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0087_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0087LowerBoundTable : List ℤ :=
  [1, 2, 129, 233, 3, 305, 2, 115, 1, 202, 163, -112, 53, 254, 73, 12, 176,
  570, 257, 537, 287, -183, -331, -220, 619]

def fractionalNearFrameSubtreeG2R0087LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0087Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0087LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
