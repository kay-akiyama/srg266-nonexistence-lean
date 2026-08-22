import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0093`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0093Mask : ℕ := 944037881881164

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0093Witness : Array ℤ :=
  #[-970, -1124, -1173, 840, -659, 1118, -393, 589, 310, 904, -733, -1683,
  -120, 2804, -365, 975, -1727, 1177, 611, 516, -1921, -2788, -222, 121,
  2177, -340, 1483, -1132, -2121, 642, -1813, -196, -1276, -151, 1284, 2537,
  -232, -1089, -1558, 382, 588, 0, -2017, 317, -1098, 697, 1877, -2234,
  -2322, 10, -679, 1855, 424, -311, -1601, 0, -3317, 448, 1299, 443, 2841,
  -286, 1880, -1849, -392, 801, -97, 2016, 1853, 541, -281, 449, 1702, 2247,
  303, -1311, 346, -681, -894, -1981, 717, 628, -245, 1342, -700, -634, 313,
  376, 2536, -439, -1365, 1291, 1621, 1617, -759, 40, -2534, 1801, -59, 925,
  -618, -1942, 1778, -856, -912, 1333, -312, 1188, 2871, -1825, -1252, -23,
  225, 597, 1688, -223, -1167, -1505, -937, 1747, -1071, 2025, 2377, 315, 0,
  -1774, 962, 3093, -389, -818, 1059, 1219, -138, -139, 1908, -1021, -551,
  1439, -591, 719, 2260, 1746, -626, 2651, 339, 1717, -280, 102, -335, 8,
  -1125, 1068, 142, -832, 1806, 1607, 1095, -517, -478, -48, 646, 892, 2507,
  3083, 300, -148, 93, 135]

theorem fractionalNearFrameSubtreeG1R0093_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0093Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0093Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0093Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0093_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0093LowerBoundTable : List ℤ :=
  [774, 5885, 3176, 1983, 1197, -3100, 677, 138, 2451, 2834, 3416, -2121,
  9482, -5243, 7449, 100, -1125, 5702, 4237, 6005, 2384, 7155, 4474, 1232,
  4112]

def fractionalNearFrameSubtreeG1R0093LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0093Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0093LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
