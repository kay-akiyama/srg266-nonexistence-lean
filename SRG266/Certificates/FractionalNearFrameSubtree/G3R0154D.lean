import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0154`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0154Mask : ℕ := 6850422058159192

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0154Witness : Array ℤ :=
  #[-82, 107, 393, -1221, 937, 341, -361, 85, -1395, 217, -180, 294, -30,
  744, -209, 865, 806, 179, 0, 500, -918, 30, -1381, -144, -788, 270, 1633,
  243, -24, -1833, 545, 123, 0, -174, 656, -726, 352, -911, 766, 988, -712,
  194, 742, -283, 88, -630, -831, 472, 238, 413, -596, 1541, -1918, -2208,
  1759, 759, -1478, 100, 1229, 1178, -657, 370, -2327, 682, -1428, 408,
  -144, 1006, -1, 520, -651, 1403, -1378, -52, -531, 127, 647, 1476, 1790,
  1210, 487, -180, 1262, -1397, 146, -198, 603, -645, -107, -1197, -1192,
  -167, -453, 40, 1827, 545, 717, 747, -1680, -465, -79, -1859, -841, -52,
  -1038, -132, 958, -160, 2507, 700, 213, -445, -589, 299, -1590, -954,
  -1163, 1015, -121, 2977, 659, -548, -302, 1559, -400, 1323, -373, 793,
  -273, -284, -1245, 1358, -139, 1421, 1860, -154, 909, -543, 777, -749,
  526, 834, -2018, 1061, -1011, 146, 742, -1203, 458, -1860, 351, 606, 0,
  2917, 2391, -1036, -944, -877, 877, 2492, -1004, -1505, -1759, 1060,
  -4041, 966, 45, 1637]

theorem fractionalNearFrameSubtreeG3R0154_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0154Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0154Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0154Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0154_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0154LowerBoundTable : List ℤ :=
  [-487, 1252, -2152, 2537, -260, -1783, 762, 378, 300, -1711, 3797, 2380,
  1376, -3519, 99, 3466, -1711, 5463, 2550, 5114, 2343, -2155, 2108, 100,
  2406]

def fractionalNearFrameSubtreeG3R0154LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0154Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0154LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
