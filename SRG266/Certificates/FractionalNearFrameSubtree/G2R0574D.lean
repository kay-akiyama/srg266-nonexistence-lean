import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0574`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0574Mask : ℕ := 6848293833786890

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0574Witness : Array ℤ :=
  #[146, -1004, 703, -160, -890, 399, -3091, -1489, -2164, -714, -1151, 650,
  2332, 1540, 1938, 1965, 2766, 609, 1515, 523, -505, 221, 1146, 102, -1065,
  1056, -1032, 18, -2810, -958, -867, 888, -1168, 2920, -1571, -1825, 1741,
  1058, 565, 248, -1278, -517, -729, -583, -1003, 1418, -232, 510, 521,
  1219, -531, -394, -584, 0, 109, -152, -428, -150, 1288, 1462, -1401, -924,
  -1209, 1524, 0, -507, -53, 268, 677, 354, 202, 383, -553, 794, -4, 1542,
  371, 394, 951, -944, 76, 1058, -1871, -74, 405, 1910, 204, 1080, 109, 8,
  724, 178, 441, 2120, 1118, -614, 111, -106, 826, 1296, 1177, -292, 347,
  -1641, -1779, 0, -318, 1065, 1031, 1291, -776, 974, -433, -379, 264, -706,
  -724, -376, -294, -191, 973, -130, 45, -89, -35, 366, 703, 420, 1299,
  -508, 188, -298, 284, -844, 1694, 626, 1168, -565, 1286, 1587, 363, -900,
  488, 18, -1067, -97, -753, 470, -813, 28, -100, 1040, 1008, -177, 579,
  263, 467, -74, 543, 695, 401, 351, 287, 1296, -1914, 1577, 946, 358]

theorem fractionalNearFrameSubtreeG2R0574_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0574Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0574Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0574Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0574_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0574LowerBoundTable : List ℤ :=
  [1018, 2932, 1189, 2398, 2940, 1633, 32, -435, 3762, -2676, 2439, 292,
  1750, 511, 2031, -867, 3803, 2143, 5562, 4436, 1758, 3591, 8360, -2201,
  485]

def fractionalNearFrameSubtreeG2R0574LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0574Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0574LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
