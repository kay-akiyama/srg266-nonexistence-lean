import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0212`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0212Mask : ℕ := 2365494714551313

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0212Witness : Array ℤ :=
  #[-1430, 608, 248, 322, -1426, 56, 357, 0, -210, -218, -64, -1182, 328,
  365, -526, -29, 193, 0, 546, -1026, 863, 540, -174, -17, 110, 289, -1103,
  -1256, 1106, 853, 67, 1477, -811, 822, 200, -1445, -1267, -13, -629, -356,
  400, 691, 446, -114, 863, -2680, -1512, 1382, 1272, 550, 317, 795, 1416,
  820, 1917, 895, 706, 892, 829, 1182, -541, 1911, 168, -803, -851, 283,
  743, -1168, 356, -590, -116, -1435, -899, -476, -270, 686, -162, -404,
  1021, 518, -1640, 164, -146, 697, 243, -347, 26, 23, 485, 195, 364, 1230,
  427, 1064, 988, 1495, 768, -829, 139, 498, -838, -314, -802, 17, 330, 648,
  37, 161, -856, 967, -338, -648, -222, -515, -344, 704, 508, 296, 965,
  -462, 203, 591, 845, 1395, -410, 80, -277, 927, -373, 61, 670, -914, 173,
  493, -691, 1409, 313, -92, -246, 179, 143, 667, -172, 121, -129, -155,
  243, 1233, 661, -41, 35, -71, 488, 1778, 847, 142, -7, -786, -189, 450,
  -38, -412, -941, -551, 96, -403, -505, -727]

theorem fractionalNearFrameSubtreeG2R0212_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0212Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0212Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0212Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0212_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0212LowerBoundTable : List ℤ :=
  [410, 1880, 1189, 1984, -1675, 1059, 2682, 32, 1183, 1844, 1673, -108,
  1416, 1833, 3705, 140, 3775, 2778, 2066, 863, -399, 898, 100, 5404, -286]

def fractionalNearFrameSubtreeG2R0212LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0212Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0212LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
