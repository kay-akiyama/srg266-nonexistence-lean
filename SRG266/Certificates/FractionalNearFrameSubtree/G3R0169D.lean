import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0169`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0169Mask : ℕ := 6857225017725544

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0169Witness : Array ℤ :=
  #[1371, -428, -591, -292, -325, 1354, 179, 1327, 168, -142, -747, 656,
  -70, 732, 958, 1618, -512, 390, 840, 902, 527, -301, -1022, 212, 169,
  -113, -380, -64, 1122, -426, 540, 1353, -439, -1044, -354, 864, 774, -326,
  -15, -1036, -366, 735, 368, -57, 887, 951, -385, -83, 29, 1510, 973, -496,
  -224, -1453, -143, -125, -1092, -889, -662, 17, 118, 506, 1263, 3122,
  -209, 1700, -16, -293, -580, 356, -968, 157, 1030, -964, 1126, -565, 703,
  25, -1075, 726, -192, 88, 433, -74, -40, -1557, -1175, 662, 950, -1125,
  990, 1695, 399, 246, -548, 2628, 64, -726, -35, 769, -227, 1050, 915, 892,
  721, 1792, 606, 7, 818, -1191, -763, -2632, 52, -205, 1051, -126, 124,
  585, -3232, 1158, 714, 1915, 1059, -516, -978, 158, -116, -650, 807, -213,
  66, 805, 948, 735, 942, 414, 839, -258, 153, 347, -725, -758, -840, 911,
  184, 760, 859, 420, -545, 647, 491, 1358, -489, 640, -1307, 1596, -26,
  885, 257, 119, -563, -370, 0, 1260, 1006, 1213, -156, 129]

theorem fractionalNearFrameSubtreeG3R0169_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0169Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0169Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0169Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0169_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0169LowerBoundTable : List ℤ :=
  [1554, 2527, 3828, 1254, 1358, 3208, 2300, 1559, 32, 3144, 2920, 1302,
  1961, 4174, 2720, 5420, 2789, 2239, -1639, 902, 823, 100, 6363, 6471,
  6191]

def fractionalNearFrameSubtreeG3R0169LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0169Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0169LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
