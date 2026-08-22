import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0008`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0008Mask : ℕ := 268070588698769

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0008Witness : Array ℤ :=
  #[-676, -466, -478, -1171, -79, -224, 446, 340, 0, 280, 458, 935, 523,
  -392, 380, 235, -87, 57, 57, -1143, -291, -634, -689, 217, -88, -474,
  -509, 369, 1166, 567, 1214, 0, 435, 896, 782, -225, 634, -145, -302, -191,
  -100, -730, -1033, 1081, 370, 27, 351, 1101, 166, 0, 240, -522, -102, 439,
  40, 693, 727, 794, 620, 11, -513, -899, -1696, -731, 914, -870, 116, 1037,
  1035, -975, 1021, 512, 393, -123, 564, -249, -47, 114, 552, -55, -360,
  -367, 364, 236, 293, 319, 48, 378, 529, 190, 178, -298, -270, -646, -533,
  274, -91, -835, -1299, -583, 292, -1191, 1099, 326, 357, -339, -93, -333,
  -1178, -245, -463, -239, -143, -288, -1055, 699, 2065, -386, 673, 297, 64,
  -256, 921, 21, 114, 270, -218, -261, 766, 408, -35, 52, 472, 919, 198,
  339, -194, 597, -46, 433, 306, -114, 754, 796, -992, -886, -446, 564,
  -203, 653, 180, 548, -343, 147, -1242, -871, -823, -69, -792, 342, 781,
  540, -865, 378, 350, -580, -282, 240]

theorem fractionalNearFrameSubtreeG3R0008_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0008Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0008Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0008Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0008_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0008LowerBoundTable : List ℤ :=
  [-559, 286, 249, -914, 31, 31, 785, 661, 640, 101, 1523, 2630, 920, 863,
  2619, 2211, -702, 209, -331, 884, -1266, 2090, 48, 2386, 2788]

def fractionalNearFrameSubtreeG3R0008LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0008Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0008LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
