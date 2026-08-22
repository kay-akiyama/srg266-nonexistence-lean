import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0157`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0157Mask : ℕ := 1039892657380144

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0157Witness : Array ℤ :=
  #[634, 897, 789, -1875, -2336, 1571, 3674, -630, -998, -1168, 4274, 1020,
  1345, 1315, 5747, 1500, 1756, 3932, 2821, 899, 2478, 1494, -1534, 773,
  -2341, -281, -2616, -3323, 2311, 4712, -325, -1824, -423, 1780, -2153,
  1492, -625, 1088, 900, -3067, 2794, 279, 993, 2037, 12, 90, 2825, -204,
  625, 2937, -3847, 1020, 110, -681, -402, 524, -2402, 2569, 3944, 397,
  -363, 969, -863, -271, 2221, -1380, 1752, 89, 3247, 2111, -1506, -398,
  -4118, 2927, -1083, 158, 0, 536, 1985, 3033, 2505, 3941, -452, 912, -275,
  0, -1220, 990, 53, 5526, 676, 1320, 4848, -261, -2045, 2091, 1159, 429,
  1312, -962, -997, 1325, -888, 165, 2895, 2560, 2113, 1056, -1514, 3347,
  -3595, -190, 4229, -188, 2990, 750, 2832, 2221, 1287, -852, -1527, 840,
  1380, -996, 499, -3128, 785, -985, 2410, 548, 86, 2314, 112, -862, 737,
  -3930, -3361, 2563, 1357, -345, -1011, 0, -2641, -3480, -36, 0, -2343,
  1783, -3143, -1451, -454, 672, 2612, 751, 432, 4610, 1777, 1990, 2575,
  3601, 3497, -5534, 1857, -945, -717, 144, 1806, 1453]

theorem fractionalNearFrameSubtreeG1R0157_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0157Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0157Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0157Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0157_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0157LowerBoundTable : List ℤ :=
  [4142, 2761, 6130, 3474, 7045, 7155, 6377, 9169, 9755, 7142, 99, 11235,
  8078, 6113, 5543, 9746, 4140, 12641, 403, 9069, 3650, 3988, 19930, 8535,
  2443]

def fractionalNearFrameSubtreeG1R0157LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0157Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0157LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
