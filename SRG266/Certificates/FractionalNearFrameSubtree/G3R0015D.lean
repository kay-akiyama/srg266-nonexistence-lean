import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0015`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0015Mask : ℕ := 815410976817734

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0015Witness : Array ℤ :=
  #[-577, 259, 1256, -511, 657, -453, -834, -514, 0, -808, 1181, 1299, 403,
  1095, 1584, 292, 891, 833, -162, 1974, 0, -297, 483, -415, -734, -550,
  1879, 454, -1, -341, -631, 1098, 403, -1122, -757, 842, -635, 1127, 204,
  759, -676, 1987, 216, 1118, 551, 0, -1520, -1086, -436, 2100, -910, 475,
  -349, -549, -768, -1579, -346, 250, 728, -695, -1171, -329, 476, 206,
  -237, 259, 91, -1089, -268, 3473, 1654, 1244, 2575, -1460, -66, -1373,
  -1024, -326, -5, -2911, -181, -894, 252, -130, 259, -468, 1390, -855,
  -372, 324, 792, 890, -1885, -429, -1348, -1848, -2415, 805, 359, 229,
  2470, 838, 348, 565, -757, 988, 851, -690, 102, 137, 1718, 1014, 821, 450,
  -341, -1898, -18, -1017, 299, -374, -28, -941, 781, 487, -476, -1701,
  -146, 643, 1773, 1055, -152, -787, 553, 1369, -386, 900, 1141, 352, -811,
  1614, -724, 1059, 365, -733, -43, 544, 202, -47, -773, 512, 615, -641,
  604, -285, 719, -120, -236, 1097, 973, 255, 536, 1016, -142, 19, 24, 185,
  1035, 1770]

theorem fractionalNearFrameSubtreeG3R0015_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0015Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0015Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0015Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0015_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0015LowerBoundTable : List ℤ :=
  [-250, 2332, -805, 4022, -1239, -352, 4963, 3367, -1668, 3714, 3444, 3775,
  -1182, 745, -1226, 1591, -1938, 5457, 2313, 6728, -1297, 2390, 5683, 310,
  3546]

def fractionalNearFrameSubtreeG3R0015LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0015Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0015LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
