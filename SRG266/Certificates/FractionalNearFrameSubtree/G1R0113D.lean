import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0113`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0113Mask : ℕ := 969034599711052

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0113Witness : Array ℤ :=
  #[23, 148, -29, 61, -109, -152, -210, -101, -98, 88, 178, 9, 102, 200,
  170, 61, -126, -4, -133, 79, -86, -8, -115, 29, 145, 161, 16, -23, -193,
  -78, 298, -238, -56, -92, 119, 173, -110, -193, 24, 170, 109, 110, 54,
  -189, -132, -131, 181, 21, -24, -9, 66, 255, 90, 39, 87, -94, 72, 264,
  -85, 62, -218, -162, 310, 91, -127, -163, -25, 103, 41, 56, 201, -20, 77,
  -16, 200, 238, 222, -3, 175, 38, 83, 33, -11, -152, -61, 131, 14, -218,
  -242, 28, -90, -17, -74, 136, 201, -17, 66, -3, 164, -43, 22, 138, 77,
  150, 145, 97, 274, 13, -16, 220, 110, 91, -25, 87, -6, 11, 32, 165, 11,
  104, -33, 63, 51, 30, -128, 18, 108, -35, 56, -23, -101, 54, -71, 126,
  -203, 75, 147, -108, -94, 263, -108, -113, -155, -53, -252, 42, -85, 43,
  -77, -45, -178, -190, -186, 337, -219, 80, -62, 60, -16, 161, -148, 169,
  37, -122, 216, -46, 26, -32]

theorem fractionalNearFrameSubtreeG1R0113_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0113Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0113Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0113Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0113_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0113LowerBoundTable : List ℤ :=
  [32, -207, 500, 2, 337, 192, 151, 246, 214, 9, 257, 370, 296, 973, 408,
  -217, 464, 775, 218, 149, 203, 285, -97, 10, 24]

def fractionalNearFrameSubtreeG1R0113LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0113Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0113LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
