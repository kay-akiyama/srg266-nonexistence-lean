import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0347`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0347Mask : ℕ := 5668900366097425

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0347Witness : Array ℤ :=
  #[-229, -42, 7, -230, 0, -52, 267, 299, 270, 172, 438, 353, -159, -130,
  -152, -183, -3, 33, 0, -103, 97, 1, -305, -38, 79, 155, 150, 66, 153, 156,
  -61, 519, 0, 232, 188, 101, 98, -175, -460, -53, 313, 185, 225, 16, -208,
  -138, -135, 89, 315, 98, 211, 92, 121, 124, 285, 31, -29, -21, -68, 77,
  183, 282, 71, 43, -40, -11, 126, -276, 89, 80, 325, 156, 149, 105, 119,
  -136, -77, 22, -94, 0, -94, 92, 130, 63, 387, 85, 152, -90, 2, 486, 51, 6,
  325, 99, -47, -147, 121, -234, 97, -90, 97, 190, -267, 13, 168, 62, 135,
  -181, -116, -275, -254, -272, 1, -55, -83, -315, -12, 214, 635, 342, 2,
  294, -122, -235, 142, -146, 256, 137, -134, 208, 167, -73, -288, 98, -125,
  -167, -46, 43, 3, -201, -19, 290, 116, -81, 73, -206, 302, 2, -247, -359,
  -58, -108, 118, -20, 141, 335, 3, -109, -129, 101, -1, 4, 117, 132, 44,
  210, -109, 32]

theorem fractionalNearFrameSubtreeG2R0347_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0347Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0347Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0347Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0347_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0347LowerBoundTable : List ℤ :=
  [266, 105, 242, 240, 695, 430, 462, 420, 542, 458, 79, 344, -6, 400, 771,
  652, -190, 612, 271, 528, 1166, 170, 1220, 614, 808]

def fractionalNearFrameSubtreeG2R0347LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0347Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0347LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
