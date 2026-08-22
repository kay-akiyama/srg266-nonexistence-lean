import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0104`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0104Mask : ℕ := 5247678709140242

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0104Witness : Array ℤ :=
  #[-2530, 8751, 241, -624, -10033, -4155, -7569, 711, 5198, -8732, -9216,
  11882, 14913, 9696, 7095, 869, 4059, -3304, 748, 11020, -1296, 8392, 2878,
  -1057, 11415, 3510, -9165, -19309, -18566, -11752, 1436, -8314, -6152,
  -3783, 8957, 13436, 12260, 12037, -5729, -2789, -15386, -3623, 14641,
  5041, 6537, 941, 2665, 1045, 5009, -7415, -986, 1261, 7528, -4893, -14482,
  -14146, -20273, 3228, -984, 10619, -4529, -2632, -4219, 4463, 420, -4295,
  -8833, 4355, 7248, 7859, 3797, -2388, 5437, -4693, 1311, -4179, 546, 9255,
  4041, 538, 5025, 505, 259, 6331, -9990, 3330, 2108, 2566, 5531, -5887,
  5506, -1687, 5427, 6851, 3203, 6880, -836, -4815, 2192, -8394, 4380, 7199,
  -4201, -4293, -8288, -2408, -8959, -2711, -4036, 1808, -3418, -3487, 0,
  9046, -419, -3157, 2405, 4880, -1691, 5934, -1470, 432, -17884, -8142,
  -13328, 5129, 4500, -2409, 2232, -2731, 4679, 2876, -987, 10238, 4636,
  6227, -3916, 3788, -4545, -7461, -3492, -8895, 3858, 126, 6221, 6090,
  2448, 3593, 5961, -11069, 5933, -5106, -2335, -3595, 9165, -7169, 0,
  -1159, 1247, 6978, -11570, 4340, 2360, -1449, 2380, -4896, -6564, -5385]

theorem fractionalNearFrameSubtreeG3R0104_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0104Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0104Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0104Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0104_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0104LowerBoundTable : List ℤ :=
  [-17834, -7154, -8808, -11376, 6523, 7462, 1000, 11911, -3169, 98, -3581,
  6365, -22342, -15656, 100, 9866, -25126, 11142, -9082, 3314, -20980,
  25010, 26435, 19661, 25133]

def fractionalNearFrameSubtreeG3R0104LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0104Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0104LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
