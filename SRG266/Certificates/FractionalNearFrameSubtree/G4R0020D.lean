import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G4R0020`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0020Mask : ℕ := 4886627775534085

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0020Witness : Array ℤ :=
  #[1853, 271, 1717, -20, 1803, -232, -571, -1337, -1452, -2568, -2747,
  1971, -95, 1397, 78, 957, 514, -26, 48, 899, 1006, 500, 143, -523, -1551,
  -1960, -781, 519, 491, 0, 343, 18, 348, 115, 174, 920, -1203, -1834, 1974,
  -472, 239, -34, -623, -1529, 1084, -375, -972, 1365, 565, 810, -367, 450,
  2919, 1661, 529, -1003, -1841, -1616, -1255, -348, -384, 1793, 599, -1970,
  -467, 2631, 2003, -1512, -1091, 1077, -460, -589, 1201, 558, 825, 499,
  660, 210, -547, 244, 392, -232, 809, 335, 889, -758, 138, 285, -21, -1041,
  779, 38, -635, -609, -1404, -592, 87, -1547, -907, -245, -1262, 683, -709,
  1765, 1694, -71, -613, -1041, 458, -1508, 0, 1298, 500, 574, -1241, 144,
  -747, -55, -391, 290, 567, 491, 1340, 1044, 678, -176, -606, -1313, 908,
  1778, 464, -427, -177, 63, 1073, -277, -1418, 1087, -818, 1581, 1001,
  -2563, 1306, 796, -693, 2276, -499, -1432, -51, -128, 1060, 2477, -915,
  -224, -3379, 890, 535, 762, -52, -1071, 726, 588, 246, -457, -487, -83,
  307, 1378]

theorem fractionalNearFrameSubtreeG4R0020_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0020Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0020Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0020Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0020_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0020LowerBoundTable : List ℤ :=
  [-1125, 795, -231, 31, -825, -288, 1554, -30, 2073, 4146, 483, -204, 1890,
  4126, 1372, 1767, 6770, 3921, 99, 99, -2204, 1599, -1890, -1571, 4279]

def fractionalNearFrameSubtreeG4R0020LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0020Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0020LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
