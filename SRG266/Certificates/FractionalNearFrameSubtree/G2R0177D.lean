import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0177`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0177Mask : ℕ := 1386774781346008

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0177Witness : Array ℤ :=
  #[1038, -372, -280, -10, -1300, -195, -1304, -905, -1969, 0, 106, 2348,
  673, 279, 1122, -275, 546, -345, -249, 732, -465, 907, -305, 864, 854,
  310, -1171, 519, 1742, 1554, 545, -479, -694, 577, -425, -1864, -1945,
  -341, -662, 1209, 235, 294, -923, -300, -1737, 420, 217, -1134, 1110, 510,
  -385, 996, -556, 286, 1273, 432, -1181, -1259, 431, -2132, -87, 348, -513,
  1600, 1617, -329, -1127, -1356, -662, -1350, 250, -171, -493, 53, 430,
  -741, -1041, 704, 374, 935, -248, 238, -349, -649, -632, 391, -2900, -742,
  -222, 86, 149, 391, -661, -204, 86, 2291, -2755, 756, 1429, 145, 411,
  1853, 469, 35, 2481, 1228, 225, -1262, -660, 1335, -439, 49, -278, -352,
  633, 758, -83, 691, 791, -276, -1552, 1721, 182, -523, 815, 716, -25, 293,
  -544, 604, 48, 740, 402, 2637, 577, 286, 1036, 1235, -1463, 2638, 952,
  -1117, -207, -335, -1306, 1173, -818, 611, -1096, -954, 425, -1528, -1529,
  -348, -163, 18, 376, -478, -1219, 205, 1181, -167, 31, -995, 0, -327, 87,
  -83]

theorem fractionalNearFrameSubtreeG2R0177_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0177Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0177Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0177Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0177_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0177LowerBoundTable : List ℤ :=
  [-1774, 741, 410, -1492, -913, 1209, 963, -1573, 300, 2362, 3561, 1365,
  99, 841, 3093, -1290, 3783, -4409, 3534, 100, 2456, -344, 242, 281, -1240]

def fractionalNearFrameSubtreeG2R0177LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0177Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0177LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
