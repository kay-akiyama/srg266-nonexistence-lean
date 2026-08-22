import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0152`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0152Mask : ℕ := 1039877711433968

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0152Witness : Array ℤ :=
  #[762, 13955, 3058, 3716, 2632, 2936, 2199, -2355, -4743, -521, 3240,
  -2361, -1064, -3106, -6294, 5786, -2179, -1038, -2539, 6236, 2217, 1657,
  4907, 2583, 1261, 4814, 4876, -1169, -2724, -4526, -486, 3716, -10523,
  -4625, 6628, 4619, -2101, -3433, -1110, 8812, 9595, 12607, 8332, 13328,
  15222, 1700, 5763, -20631, -16257, -11056, 1844, -95, 7450, 8231, -11191,
  -13288, -1956, 1823, 0, -996, -590, 3235, 1467, -3145, 991, -5022, -120,
  -137, -1373, 1607, 1500, -4137, 1315, -1554, -1143, -147, -1196, -3202,
  -3007, 5264, -2277, 3613, -58, 3684, 7951, 4357, 3388, 315, 0, 1812, 7556,
  -2165, 2462, -3166, 0, -5452, -1084, -1937, -4988, 1806, 1369, -3938, 727,
  4984, -2268, 512, -3944, -3819, -1303, 2532, -326, 4230, -6516, -5235,
  -2500, -4259, 3093, -3909, -4686, 1244, 625, 3721, 358, 777, -5702, 5025,
  1750, 3391, -3920, 6542, -778, 1718, -4830, 5713, 2507, -394, 3122, -2903,
  945, 5793, 5618, 1948, -2123, 5178, 4430, 2560, 1681, -620, -9801, -6978,
  -2865, 3756, -544, -4338, 2549, 1966, 4235, 6022, 3717, 3114, 2066,
  -11094, -108, -8204, -1559, 2729, -5421, 5985]

theorem fractionalNearFrameSubtreeG1R0152_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0152Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0152Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0152Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0152_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0152LowerBoundTable : List ℤ :=
  [1067, 32, 3550, 6707, 17126, 32, 5951, -1359, -3809, -7237, 13924, 3469,
  -5224, -933, 13394, -550, 723, 100, -7206, 5610, 11186, 10056, 24224,
  15800, -947]

def fractionalNearFrameSubtreeG1R0152LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0152Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0152LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
