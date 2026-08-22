import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0155`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0155Mask : ℕ := 1039887972485552

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0155Witness : Array ℤ :=
  #[227, 31, -285, 141, -258, 520, -262, -155, -256, -122, 451, -109, 455,
  202, -277, -136, -814, -383, 74, 350, 309, 0, 81, 426, -188, 62, -120, 47,
  86, 23, -394, 62, 48, 145, 636, 361, 449, -46, -711, -239, 671, 164, 483,
  234, 23, -205, 85, 164, -355, -79, 387, 337, 342, -300, 367, -640, 643,
  741, -83, -562, -824, 495, 332, 17, 1076, -146, 230, 368, -99, 98, -185,
  -106, 147, -146, -220, 72, -283, 453, 221, 223, 292, 80, 87, 48, 26, -212,
  336, 241, -420, 148, -11, -336, -140, 57, -66, 40, -144, 206, 434, -81,
  -90, 328, -100, -222, 373, 266, 490, -162, -391, 59, -707, -424, 394, 333,
  0, -108, -96, -97, 86, 184, 210, -271, 196, -103, -202, -420, -300, -34,
  185, 431, -289, 171, 394, -24, -39, -340, 215, -142, 38, -199, 181, -260,
  -198, 6, 169, 27, 141, -417, -29, 0, -370, 77, 356, 0, 55, 562, -171, 99,
  275, -29, 126, -354, -90, 163, -64, -369, 316, 128]

theorem fractionalNearFrameSubtreeG1R0155_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0155Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0155Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0155Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0155_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0155LowerBoundTable : List ℤ :=
  [109, -159, 32, 32, 33, 341, 1619, 32, 1593, 100, -210, 100, 101, 1240,
  -782, 917, 1320, 892, 1030, 133, 890, 554, -267, 95, 791]

def fractionalNearFrameSubtreeG1R0155LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0155Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0155LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
