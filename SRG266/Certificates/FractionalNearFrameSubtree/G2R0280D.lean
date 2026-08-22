import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0280`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0280Mask : ℕ := 5372937403730536

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0280Witness : Array ℤ :=
  #[75, -45, -77, -20, -1, 174, 65, -38, 190, -82, 54, -4, 5, -97, 11, -79,
  -179, -45, -39, 61, 91, 57, -43, 41, 105, 19, 211, 246, 168, 154, 134,
  152, 77, 25, 47, 73, -43, 136, 58, -194, -162, 0, 4, 165, 118, 49, 46,
  103, 103, 52, 237, -114, 21, -4, -45, 13, 0, 117, 54, 59, 213, 4, 88, 154,
  0, 63, 279, 76, -24, -63, 150, 62, -70, -90, -56, 80, 111, -5, 41, 58, -9,
  11, -25, 139, 56, 14, -22, -15, -30, 38, -53, 23, 158, -11, -97, -8, 37,
  -58, 102, -69, 32, 113, 281, -150, -99, 54, -58, 54, -58, 72, -12, -55,
  -109, 11, 34, 93, -51, 69, 10, 76, -101, 43, -99, -73, 56, 58, -72, -22,
  -153, -4, 122, 175, -93, 32, 74, 3, -68, 119, -82, -188, 21, -5, -44, -18,
  176, 99, 117, -39, -2, 203, 168, 86, 44, 102, 121, -276, -14, -30, 1,
  -204, -10, 98, 23, 219, 146, -38, -223, 98]

theorem fractionalNearFrameSubtreeG2R0280_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0280Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0280Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0280Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0280_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0280LowerBoundTable : List ℤ :=
  [251, 74, 372, 272, 2, 384, 377, 338, 542, 579, 173, 280, 347, 231, 585,
  256, 1006, -171, -130, 711, 251, 243, 191, 507, 422]

def fractionalNearFrameSubtreeG2R0280LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0280Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0280LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
