import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0615`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0615Mask : ℕ := 9609416853934601

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0615Witness : Array ℤ :=
  #[436, 0, 68, 131, -1671, 464, -3925, 0, -4101, -1332, -1354, 656, 2916,
  1518, 1445, 2379, 3075, 1123, 68, 999, 3147, -1363, 2258, -534, -1085,
  956, 339, -1070, -1149, -1589, -774, 563, -730, -1662, 1649, -1427, -2130,
  1480, 2732, 2966, 14, -1234, -1090, 406, 2292, 1135, -2360, -167, 872,
  1158, 109, 936, 822, 250, -1327, -20, 517, 1158, 697, -2409, 500, 1577,
  -1256, 612, 1647, -1332, 1836, -1332, 535, 20, -1732, -230, -209, -425,
  119, -1360, 682, 1169, -1918, 655, -69, -1758, -364, -1422, -1172, 1023,
  1229, 1108, 238, 123, 108, 1076, 1042, 275, 1492, -152, -400, 717, 1106,
  1594, -848, -1336, -2478, -979, -1035, 367, -1413, 318, -401, 1837, 698,
  1882, 1881, 2035, -3577, 401, 1366, 1541, 685, 1775, -677, 1320, 1026,
  234, 627, 126, -1032, -748, -283, -1395, 1476, 324, 1285, 289, 867, 294,
  -1099, -1185, 1790, -375, -1828, -1101, -573, -318, 1379, 410, 1297,
  -1747, 34, 40, -363, -788, 750, 223, -374, -1100, 2619, 1869, 4604, 872,
  -62, 218, 668, -1605, -893, -181, -16, -110]

theorem fractionalNearFrameSubtreeG2R0615_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0615Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0615Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0615Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0615_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0615LowerBoundTable : List ℤ :=
  [-742, 2569, 31, -685, 1841, 31, 33, 3307, 1169, -203, 10712, 12163,
  -3097, 1757, 2030, 6911, 1516, 871, 4032, 2115, 98, 2747, 3794, -2695,
  3409]

def fractionalNearFrameSubtreeG2R0615LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0615Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0615LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
