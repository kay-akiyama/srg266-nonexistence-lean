import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G4R0042`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0042Mask : ℕ := 5471842305819426

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0042Witness : Array ℤ :=
  #[360, 3409, 823, 874, 1928, 1727, 0, 1807, -255, -1032, -691, -731,
  -1126, -2344, -4056, -2207, -2690, 2012, -1608, -420, -2158, 1322, 126,
  297, -1175, -644, 2860, -491, 2374, 2582, -2104, 1618, -709, -841, -468,
  -640, -553, 211, -143, 2861, 2206, 1163, 567, 2212, 2739, 415, 1531, -59,
  -1981, -1695, -67, -857, 1822, -391, -1406, -1300, -1658, -1728, -2358,
  1187, 376, 1291, 436, 1900, 1735, 1120, -978, -1438, -305, -693, 396,
  -3220, 812, -762, -1078, 1146, 238, -553, 1169, -542, 665, 495, -1207,
  1376, 991, 130, 1626, -798, -1178, 1387, -892, -441, -12, -1961, 153, 945,
  1095, 1729, -3165, 441, -691, 277, -1405, -591, 1159, 1170, 429, 1693,
  194, -1190, -2706, -1003, 1026, 1012, 2320, 100, 1801, -617, 855, -905,
  750, 1029, -173, -1364, 647, 0, -644, -29, -2142, 56, 256, -291, 1335,
  570, -1762, -570, -527, 83, 1340, -668, -18, 0, 1673, -614, 490, 5207,
  -885, -1490, -252, -1060, 861, 1380, 1284, 1230, 1056, -831, 334, -302,
  -1219, 548, 2454, 956, 1446, 649, -801, -158, -2096, 655]

theorem fractionalNearFrameSubtreeG4R0042_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0042Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0042Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0042Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0042_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0042LowerBoundTable : List ℤ :=
  [-755, 2198, 1323, -3637, 1482, -277, 5248, -780, 705, 622, 5053, 10655,
  -6217, -4093, 3486, 1976, 4367, -4285, -4615, 1668, -1395, 5090, 9239,
  1087, 6002]

def fractionalNearFrameSubtreeG4R0042LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0042Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0042LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
