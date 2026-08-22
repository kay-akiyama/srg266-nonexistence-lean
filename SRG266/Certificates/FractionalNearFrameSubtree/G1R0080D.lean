import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0080`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0080Mask : ℕ := 899211148765473

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0080Witness : Array ℤ :=
  #[199, 650, 262, 41, -627, 1047, 0, -1212, 212, -807, -252, -1183, 97,
  247, 1047, -650, -332, 1435, 236, -123, -134, -277, -1525, -612, 2115,
  -270, -1695, -1689, 907, 1140, 702, 1672, -190, -1039, 367, 66, 1326,
  -2619, 972, 259, 504, -251, 846, 314, -388, 79, 599, 15, -628, -353, -505,
  175, 860, 1030, -804, 1758, -524, -845, 869, 460, 777, -59, 949, -689,
  142, 1167, -580, 634, -1858, 645, 805, 628, 2, -183, -312, -295, -1386,
  1603, 341, -1060, 1900, 1180, 601, 1244, 743, -605, -668, -947, 1518,
  1443, 508, 307, -20, 389, 83, 406, -288, 1083, 1905, -1723, -1509, 904,
  143, 854, 147, -100, -1886, 846, -1686, -1312, -907, -39, -62, -634, -531,
  -593, 3259, 3522, -1514, -241, -1146, -1898, -1833, -257, -795, -1068,
  -1367, -1405, -154, 1667, 1935, 1882, -488, 215, -591, 1118, 1197, -520,
  2040, -1328, 1007, -1585, -898, 1213, -4, 213, 737, -1413, 606, 400, -714,
  -480, 444, 1144, 1703, -239, 703, 511, -795, 1683, 720, 1248, 308, 870,
  -260, 292, -1489, 2128]

theorem fractionalNearFrameSubtreeG1R0080_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0080Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0080Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0080Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0080_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0080LowerBoundTable : List ℤ :=
  [89, 2086, 2316, 1471, 33, 989, 881, 33, 767, -62, -399, 1146, 3090, 165,
  5550, 1352, 2522, 301, -2210, 3189, 3010, 101, 1463, 3611, 5413]

def fractionalNearFrameSubtreeG1R0080LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0080Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0080LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
