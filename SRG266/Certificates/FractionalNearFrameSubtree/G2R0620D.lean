import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0620`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0620Mask : ℕ := 9678849072153874

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0620Witness : Array ℤ :=
  #[-152, 101, 7457, 5402, -2987, 3332, -560, 0, 2697, 943, -2923, 2437,
  226, -1372, 9956, 5368, -864, 4494, 1425, 2284, -917, -486, -1336, -1281,
  1013, 2105, 1328, 1731, 3052, 284, 1083, -304, -5733, 2301, 4389, 439,
  1040, 1529, 851, -215, 364, 4108, 1247, 10668, 6466, 1476, 5073, -4408,
  320, -3712, -711, 685, -2375, -3177, 2714, 2735, 3426, 6624, 5219, -1017,
  -1697, 676, 952, 2355, -742, 1927, 3444, 1574, 3685, -579, 2859, -2150,
  -515, 4952, -744, 3545, 2458, 1597, 5345, 7711, 1242, -150, 1002, -5266,
  -1835, 7871, 1863, 3444, -511, 1284, 2499, 400, 6386, 6609, 3946, -3927,
  2339, -1647, -688, 153, 3314, -849, 2985, 3393, 5805, 2185, 866, 350,
  -1731, -2637, -3633, 0, 2194, 1449, 2392, 2048, 356, 133, -2874, 2708,
  1150, 843, 3199, -1609, 4897, 475, 145, 2065, -3180, -1686, 10845, 2690,
  -665, -1097, -1906, 443, 1802, -175, -1250, 5117, 4235, 1267, -951, -1567,
  -7538, 651, -706, -735, 4231, 2122, 157, 3302, -919, -3921, -5732, -1954,
  0, -1874, 3386, -2112, 1080, -2834, -1793, -5694, -6558, 1546, -9051,
  4009]

theorem fractionalNearFrameSubtreeG2R0620_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0620Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0620Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0620Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0620_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0620LowerBoundTable : List ℤ :=
  [8087, -3456, 14094, 13178, 7750, 8581, 13382, 16215, 17425, 2621, 13987,
  9392, 164, 8576, 26862, 21712, 24112, -3716, 17138, 19860, 24846, 20925,
  929, 322, 3453]

def fractionalNearFrameSubtreeG2R0620LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0620Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0620LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
