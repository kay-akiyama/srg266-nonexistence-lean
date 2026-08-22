import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0205`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0205Mask : ℕ := 2355552938611729

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0205Witness : Array ℤ :=
  #[666, 330, -174, 117, -214, 593, 510, 816, 0, 48, 889, -39, 47, -230, -3,
  105, 0, -1112, 645, 182, -599, -560, -1512, 126, 122, -449, 469, 104,
  1162, 1204, 766, 1468, 1284, 112, -208, 545, 31, -19, -925, -1239, 817,
  648, 152, 707, -8, 138, -780, 568, -804, -1225, 113, 1199, 174, -141,
  -754, 1264, -5, -442, 356, 1066, 441, -391, -5, 316, -103, -467, 987,
  -101, 374, -427, 225, 331, 262, -294, -18, 226, 333, 50, 287, 89, 138,
  -559, 591, -126, 216, 1223, 609, -154, -264, 81, -147, -472, 1673, 100,
  -426, -315, -913, -315, 515, 1074, 672, -817, 437, -821, -145, -344, -268,
  -38, 486, 157, 326, -148, -1081, 793, 379, -721, -388, 286, -59, -267,
  -230, 737, 637, 181, -773, -1196, 189, 1251, -460, -234, -97, 335, 341,
  -814, -673, 418, -199, 425, 95, -671, 585, 665, -1024, 461, -82, -714,
  619, -50, -632, 367, 1046, 104, -739, 157, 555, -501, -36, -806, 39, -267,
  1017, -355, -1316, -874, -441, -1230, 0, 37]

theorem fractionalNearFrameSubtreeG2R0205_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0205Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0205Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0205Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0205_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0205LowerBoundTable : List ℤ :=
  [-547, -1414, -408, 33, 629, 2710, 650, 801, 844, 460, -736, -606, -2013,
  2922, 678, 714, 1604, 1369, 1534, 3279, 897, -1890, 1467, 2837, 1243]

def fractionalNearFrameSubtreeG2R0205LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0205Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0205LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
