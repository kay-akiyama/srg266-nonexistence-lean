import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0011`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0011Mask : ℕ := 828583500816643

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0011Witness : Array ℤ :=
  #[-22, 60, 139, -547, -106, -398, 840, 496, 311, 573, 261, -753, -1083,
  -267, -608, -249, 122, -34, -234, 72, -134, -553, 104, -113, 299, -623,
  -63, 658, 359, 238, 282, 0, -601, 135, 390, -362, 687, 449, -360, -349,
  58, -351, 275, 9, -322, 439, -212, 382, -92, -515, 117, 80, 291, 733, 608,
  92, -13, -164, -25, -179, 318, -85, -344, 187, -628, -21, -43, 166, 14,
  36, 172, 628, 141, -161, -318, -622, 245, 196, -107, 56, 395, -169, -645,
  982, 446, -262, -78, 54, 142, -357, -421, 272, 121, 317, -135, 257, 107,
  369, 335, 367, 114, 610, -62, -105, 226, -698, -90, -27, 160, 176, 32,
  106, -34, 775, 578, -125, -620, -770, -184, -304, 646, -44, 258, 220, 112,
  -116, -229, -487, -236, -52, -6, -214, 372, 368, -130, -396, -266, -355,
  0, 143, -249, -340, 286, 69, -113, 439, 407, -329, -208, 278, -698, -52,
  26, 119, -69, 318, 687, -514, 439, 494, 788, 421, 87, -184, 134, 350, 739,
  205]

theorem fractionalNearFrameSubtreeG5R0011_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0011Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0011Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0011Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0011_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0011LowerBoundTable : List ℤ :=
  [-45, 682, 1426, 32, 625, 32, 58, -155, -183, 828, 1457, 101, -712, 2369,
  1327, 1890, 988, 393, 223, 99, 450, -165, 100, 457, 434]

def fractionalNearFrameSubtreeG5R0011LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0011Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0011LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
