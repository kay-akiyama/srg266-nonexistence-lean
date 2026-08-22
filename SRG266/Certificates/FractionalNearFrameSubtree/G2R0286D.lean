import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0286`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0286Mask : ℕ := 5385085613970058

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0286Witness : Array ℤ :=
  #[-2391, -374, -1447, -2273, -381, -1641, -30, 848, 707, 181, 1217, -103,
  -342, 558, 431, 1872, -1673, -121, -1222, -1365, -231, 429, 1853, 1425,
  1016, -183, -153, -1296, -1906, -1063, -741, -145, -157, 136, -103, -884,
  77, -537, 475, 1735, 749, 43, 105, -706, 249, 19, -1453, -378, 916, -4,
  152, -107, -1903, -32, -817, -2056, -2474, -807, 11, 1325, 532, 986, -305,
  1052, 647, 357, -385, 123, -1095, -37, 415, 852, 435, 525, -1256, 986,
  772, -534, 1033, 385, 336, 648, 1548, 1161, 57, 1207, 1025, -391, 28,
  1228, 576, 38, -548, -2288, -1020, 791, 2182, -406, 639, 1486, 213, 502,
  -331, -2403, 618, -359, 229, -357, -170, 36, -112, -740, -152, 1082, 1088,
  -518, 402, -1122, 305, -1882, -1257, 2001, 1997, -481, -1917, -1375, -428,
  740, 1188, -119, 11, -463, -324, -77, 2118, -882, 1866, -381, 758, 384,
  -790, -215, -188, 83, 4, 1225, 179, -93, 133, -684, -549, 48, 894, 2857,
  317, 730, 923, 781, 853, 1858, 638, 862, 426, -616, -1081, 894, 3577, -14]

theorem fractionalNearFrameSubtreeG2R0286_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0286Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0286Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0286Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0286_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0286LowerBoundTable : List ℤ :=
  [138, 3574, 1882, 569, 628, 32, -788, -814, -1350, 1343, -1675, -525,
  3756, 3220, 2179, 4703, 2905, 1270, -2369, -684, 1290, 6833, -1890, 100,
  5151]

def fractionalNearFrameSubtreeG2R0286LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0286Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0286LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
