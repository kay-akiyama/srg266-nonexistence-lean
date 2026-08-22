import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0032`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0032Mask : ℕ := 954026157580938

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0032Witness : Array ℤ :=
  #[768, 164, 162, 361, -105, 1129, 446, 658, -2264, -97, -675, -132, 737,
  -552, 395, -128, 1159, 409, -771, 1043, 737, 84, 692, 1125, 2087, -240,
  -1436, 572, -374, -1268, -699, -669, -63, 1128, 401, 649, 1355, 422, 565,
  66, 184, 55, -568, 637, -748, 385, -6, 579, 1173, 1789, 66, 162, -302,
  -57, -1089, -770, 17, -45, 484, 0, -350, 535, 461, 890, 1108, -110, 206,
  -33, 608, 1229, 1220, 2067, 204, -870, 1124, 173, 185, 1230, 656, 1136,
  687, 177, -122, -1653, -915, -273, 746, 322, 1287, 72, 113, -853, 521,
  1170, 119, 76, 620, 117, -1085, -10, 7, -83, 32, 6, -263, -54, -1416, 359,
  -476, 1145, 321, 1377, -981, -496, -422, -599, 1166, -1279, 295, 658,
  -159, 401, -1885, 147, -1401, -274, -141, 262, -160, 0, 775, -793, -3255,
  321, -82, -1812, 1059, 1984, 862, 59, 1012, -1115, -476, 1331, 1222, -26,
  -653, -105, 46, 376, -277, -34, 715, 524, 1246, -537, -391, -217, 850,
  1866, -1597, 2106, 1040, -466, 81, -234, -393, 762]

theorem fractionalNearFrameSubtreeG3R0032_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0032Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0032Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0032Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0032_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0032LowerBoundTable : List ℤ :=
  [382, 1046, 950, 903, 3909, 319, 1298, 2099, 2468, 937, -1499, 102, 2878,
  5321, 100, 258, 1438, 5609, 100, 1530, 1390, 3079, 8464, 2914, 3115]

def fractionalNearFrameSubtreeG3R0032LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0032Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0032LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
