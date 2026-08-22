import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0360`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0360Mask : ℕ := 5713994075283850

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0360Witness : Array ℤ :=
  #[198, 113, -2, 204, 0, 69, -231, 494, 340, -113, -599, 196, -316, 593,
  723, -270, -84, -163, -62, 12, 367, 286, 667, -174, 86, -381, -168, 127,
  103, 0, -49, -187, 468, 473, 157, 468, 156, 169, 170, 150, -148, 289, 202,
  178, 1, 763, 340, 76, -242, -399, -425, 37, 1, 244, -275, -205, 313, -71,
  -62, -27, 37, -149, 381, 95, 236, 339, 0, 186, -254, -225, -141, 165, 348,
  -43, 620, 308, -185, 259, -89, 85, 509, 633, 190, 79, 356, -151, -40, -93,
  91, -61, -144, 637, -230, -9, -292, 233, 428, 138, 133, -111, -622, -424,
  -95, -20, -479, 98, 247, 175, -82, 80, -649, 9, 70, 76, 483, -177, 836,
  657, 193, -21, -361, -306, 106, 132, 19, 183, 22, 325, -233, 39, 268, 3,
  356, -254, 747, 606, -311, 635, 93, -464, -174, 627, 334, -242, 226, 2,
  345, 10, 410, 470, 1029, 124, -270, -741, 279, 422, 0, -200, 115, -49,
  469, 257, -652, 145, -158, -96, 218, 379]

theorem fractionalNearFrameSubtreeG2R0360_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0360Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0360Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0360Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0360_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0360LowerBoundTable : List ℤ :=
  [794, 1047, 742, 625, 1183, 32, 1200, 1565, 1246, 1945, 2748, 1719, 721,
  1774, 629, -271, 526, 325, 1027, 3788, 537, 894, 1380, 101, 1678]

def fractionalNearFrameSubtreeG2R0360LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0360Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0360LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
