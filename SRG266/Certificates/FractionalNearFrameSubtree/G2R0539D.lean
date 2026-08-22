import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0539`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0539Mask : ℕ := 6833149809697542

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0539Witness : Array ℤ :=
  #[48, -7, 4, 13, -33, 24, 127, 192, 86, 60, 130, -152, -34, -109, -83,
  -95, -4, -134, -115, -179, -18, -24, 96, 81, -71, -31, 161, 35, 96, 129,
  104, 121, 33, 41, 41, 46, 158, -39, -26, -124, 105, 183, 65, 94, -111,
  -91, 27, -60, -180, 19, 0, -10, 87, 19, 198, 7, 91, 131, 0, -11, -140, 32,
  -30, -15, -101, -82, 43, 167, 135, -41, 81, -85, 1, 34, -26, 177, 100,
  -120, 18, -8, -61, -105, 23, -73, 29, 31, -29, -21, 3, 73, 7, -7, 97, 121,
  74, 119, 44, 79, 13, 107, 69, 31, -141, 23, -99, -49, -111, 49, 72, 31,
  44, 47, 13, 33, 16, -14, 153, -78, -18, 10, 245, 98, -42, 115, 21, -2,
  -90, 123, -25, -162, -141, 5, 13, -65, 17, 33, 41, 23, 162, 15, -3, 58,
  -159, 112, 86, 81, -117, -45, -84, 116, -28, 22, -39, 3, -1, -83, -128,
  82, -43, 50, -179, 12, -53, -45, 80, 10, 17, -76]

theorem fractionalNearFrameSubtreeG2R0539_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0539Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0539Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0539Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0539_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0539LowerBoundTable : List ℤ :=
  [49, -37, 137, 2, 152, 143, 81, 197, 151, 124, -60, 378, 133, 414, 278,
  63, 192, 111, -74, 214, 10, -16, 377, 493, 617]

def fractionalNearFrameSubtreeG2R0539LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0539Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0539LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
