import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0100`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0100Mask : ℕ := 5541797936473362

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0100Witness : Array ℤ :=
  #[208, 19, 558, 158, 329, 230, -351, 10, 14, -144, -56, -2, 69, 94, -152,
  -310, 58, -76, 207, 22, -23, -101, -335, -441, -131, -269, 295, 169, 473,
  120, -17, 195, 327, -89, 188, -287, -95, 311, -70, -156, -59, -134, 47,
  178, 27, 155, 295, 126, -213, -216, -236, 219, 69, 63, 93, 207, -178, 39,
  -51, 142, -264, 564, 211, 76, 274, -62, 3, -213, -320, 35, -83, 249, 197,
  -36, -182, 277, -23, 16, -334, 331, -15, 244, 241, -106, -62, -95, -255,
  97, 184, -130, -130, 194, 149, 274, -270, 120, 173, 99, 345, -76, -321,
  115, 170, 143, 67, 87, -115, -179, -326, -551, -206, -222, -89, 212, 306,
  63, -72, 381, -38, 229, 111, -138, -314, 238, -71, 121, -74, -119, 106,
  413, 85, 0, 206, -56, 113, -36, 0, -245, 349, 166, -46, 259, -129, -195,
  264, -77, -3, -108, -70, 263, -113, -72, -89, -108, 290, -184, -22, -16,
  -70, -153, -29, -129, 11, -141, 223, -259, -178, 460]

theorem fractionalNearFrameSubtreeG5R0100_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0100Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0100Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0100Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0100_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0100LowerBoundTable : List ℤ :=
  [-77, 52, 349, 236, 3, 182, 186, 88, 349, 670, -297, -369, 27, 620, -282,
  943, 1238, -332, 518, 1590, 10, 148, 10, 775, 775]

def fractionalNearFrameSubtreeG5R0100LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0100Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0100LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
