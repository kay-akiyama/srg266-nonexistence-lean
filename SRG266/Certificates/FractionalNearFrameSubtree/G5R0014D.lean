import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0014`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0014Mask : ℕ := 1006793335472195

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0014Witness : Array ℤ :=
  #[-3450, -3634, 1149, -1943, -3320, 357, 3558, 1474, 3310, 4687, 9899,
  -8131, 4595, -4580, 0, -3095, -5100, -2958, 479, 4283, -3247, 1972, 0,
  -1800, 1571, -2892, 2289, -479, 0, 3686, 1905, 2648, -4402, -931, 4241,
  -598, -2824, -502, 2010, 3243, 0, -1935, 2175, 1221, -139, 516, 500,
  -6964, -2828, 2542, -716, 2548, -293, -2412, 1266, 4124, 5625, -5229,
  -2944, 1605, 1202, -3296, -674, 2343, -298, 439, 5870, 2258, -5266, -6791,
  805, -1855, 331, 314, -4854, 2622, -2612, -5375, 2823, 3062, -2273, -1321,
  -3002, -5913, -2307, -515, 2707, 2296, 2015, -55, 4652, 2641, -1761, 5219,
  8083, -3036, -2569, -1063, 1041, 3444, 590, 5081, -1698, -2024, 1500,
  3558, 2550, 3177, -539, 7020, 1343, 1992, -1182, -2070, 4016, -486, 3608,
  527, 4713, 3742, 351, 84, -1724, 5805, -7396, 3807, 995, -4877, 2346,
  4489, 4618, -1685, -654, -4232, -3227, 8588, -6041, 6013, -4344, -5030,
  7168, 3626, 970, -491, 1151, 1780, 5002, 2847, 3832, -2703, -3290, 643,
  -2600, 1673, 4253, 5027, 7403, 699, -6541, 933, 3943, 915, 2696, -1534,
  3449, 3308, 2338, -1560]

theorem fractionalNearFrameSubtreeG5R0014_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0014Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0014Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0014Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0014_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0014LowerBoundTable : List ℤ :=
  [-308, 11892, 7772, 3115, 32, 7936, 2977, 5737, 32, 11470, 12881, 31439,
  15986, 17707, 3584, 14642, -3271, -9700, -7432, 9645, 98, 3211, 18199,
  3102, 2556]

def fractionalNearFrameSubtreeG5R0014LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0014Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0014LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
