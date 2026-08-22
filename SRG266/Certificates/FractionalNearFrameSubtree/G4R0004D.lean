import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G4R0004`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0004Mask : ℕ := 936555774413059

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0004Witness : Array ℤ :=
  #[305, 118, -274, -848, -402, -74, 1201, -1779, -854, -279, 2693, 580,
  1368, -1557, -914, 274, -178, -814, -1272, -983, -1103, -1412, 764, -1419,
  -485, 0, 2629, 1440, 1780, -764, 951, 0, 1297, 695, 24, -929, 1067, -42,
  0, -151, 157, -275, 1565, -933, -249, 440, -219, -1129, 827, -173, 174,
  126, 505, 257, -398, -459, 1376, 622, 1068, -528, -1493, 191, 1225, 1321,
  -441, 595, -204, 593, -724, 1280, 514, 43, 126, 932, -138, 329, 1026,
  1426, 18, -1064, 123, 1466, 700, -42, 1649, -124, -393, 1334, 1014, -39,
  -640, 1195, 436, 223, 17, 1569, 1317, 526, 19, -378, 1305, 612, 2012, 825,
  100, -2312, -317, 0, 1831, -1268, 531, 1279, -1661, 960, -298, -2208,
  -997, -302, 1133, -963, -688, 363, -1843, -724, -73, 1451, 66, -405, -520,
  1111, -348, -1132, -664, 229, -1038, -45, 716, -206, -166, -1087, 0, -822,
  -102, -36, -742, 1211, -1418, -1347, -1942, -1518, -109, 507, 726, 1670,
  -641, 165, -711, 16, -700, 1227, 1687, 742, -715, 1555, -1041, 65, -972,
  1430]

theorem fractionalNearFrameSubtreeG4R0004_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0004Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0004Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0004Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0004_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0004LowerBoundTable : List ℤ :=
  [309, -1989, 4000, 32, 33, 2014, 1933, -2211, 34, 100, 100, -6771, -4267,
  4826, 7353, 99, 6512, 4412, -463, 681, 2116, -1376, 10400, 738, 2774]

def fractionalNearFrameSubtreeG4R0004LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0004Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0004LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
