import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0619`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0619Mask : ℕ := 9656567080796748

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0619Witness : Array ℤ :=
  #[-7739, -2009, 558, -2946, -2366, 3412, 1107, 1942, 3264, 1861, 1864,
  878, -3268, 1190, 0, 3246, -3060, 672, 1935, 299, -340, -3007, -562,
  -1339, -2210, -3365, 630, 3923, 4773, 3575, 1086, -1089, -1750, 675,
  -3364, 2543, 3015, 2655, -3686, 1260, 452, 7401, 4631, 0, 725, 1128, 2641,
  -1356, 4694, -2476, 2432, 2237, -4406, -1464, 4236, 2392, 3283, 4171,
  -2184, 3698, 1453, -565, 1167, -6140, 2405, -4340, 1704, 1070, -5082,
  1965, -3991, 3928, -145, 3971, -1990, 3045, -109, 1013, 1282, 1141, -1691,
  -5540, -3131, 5190, -2224, -471, 1090, -2130, 2869, -716, 4094, 1617,
  -492, 5066, 2335, 2152, -1329, 3853, 2150, 5159, 3612, -1040, -6810, 1165,
  -2427, 3210, 4996, 4085, 3940, 2065, 1228, -1333, -1506, 881, -926, 3516,
  -684, -2459, 171, -4598, 492, 6066, 2480, -616, -770, 1792, -1311, -2185,
  1142, 529, -2873, 1027, -4836, 1650, -1646, -1764, -388, 2278, -8097,
  3484, 129, 1137, -2418, -2037, 3049, -1554, 1852, 4852, 1000, -2113, 1874,
  -6815, 6162, -4144, 6376, 2844, 6057, -480, -6690, 2674, -4558, 6350,
  -2996, 8258, -2278, 1034, 1654, -222]

theorem fractionalNearFrameSubtreeG2R0619_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0619Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0619Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0619Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0619_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0619LowerBoundTable : List ℤ :=
  [1006, 5128, 7582, 6547, 3798, 2918, 31, 5125, 3450, 2096, 101, 19713,
  10451, 8050, 18094, 16408, 15189, -13907, 2822, 22883, 16419, 13854,
  -5800, 6622, -1200]

def fractionalNearFrameSubtreeG2R0619LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0619Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0619LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
