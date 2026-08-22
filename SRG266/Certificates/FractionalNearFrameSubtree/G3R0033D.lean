import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0033`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0033Mask : ℕ := 954028288222346

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0033Witness : Array ℤ :=
  #[123, 52, 83, 187, 359, 273, 253, -100, -479, -80, 138, 49, -272, 75, 0,
  -685, 305, 384, -312, -198, 31, -341, 876, 71, 120, -792, -96, 197, 5,
  -474, 336, -20, -147, 133, 835, 86, -930, 415, -225, -122, -287, -920,
  296, -960, -576, 50, 972, 950, 119, -42, -351, -472, -290, 20, -97, 115,
  131, -84, -15, 0, 1186, 543, -416, 169, 493, -290, 342, 181, -368, -1129,
  689, 686, 557, -36, -588, 598, 55, -247, -2, -468, 621, 1001, -10, 36,
  299, -234, 494, 724, -17, -982, 27, -30, -215, 274, -322, 96, -67, -155,
  1023, 218, -118, 117, -154, 234, 75, -278, -705, -364, -15, 421, 179,
  -158, 586, 536, 52, 526, 311, -528, -283, 151, 94, -827, -229, 138, 696,
  457, -573, -391, -226, -810, 0, 616, -1385, -871, 449, -390, -471, 260,
  585, 704, 293, 456, 218, 615, -103, -420, 241, 945, -164, 660, 281, 1257,
  -133, -335, 989, 885, 656, 67, 331, -17, -677, 714, 341, -414, 589, -78,
  634, 716]

theorem fractionalNearFrameSubtreeG3R0033_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0033Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0033Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0033Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0033_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0033LowerBoundTable : List ℤ :=
  [284, 1188, 921, 1108, 595, -262, 906, -322, 1125, 1554, 1461, 554, 439,
  33, -788, -353, 2492, 494, 2186, 567, 99, 3193, 1806, 2070, 1216]

def fractionalNearFrameSubtreeG3R0033LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0033Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0033LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
