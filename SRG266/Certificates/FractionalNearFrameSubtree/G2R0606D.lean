import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0606`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0606Mask : ℕ := 7042881652626950

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0606Witness : Array ℤ :=
  #[-867, -390, -1543, -944, 1162, -764, -1098, -1985, -1667, 586, -2045,
  1958, 2994, 2410, 623, 2549, 2371, 2330, 1539, 3600, 1758, 1954, -195,
  491, 2126, 1484, -655, -3897, -6050, -2077, -2854, -4866, 239, 241, 345,
  -949, -1781, -224, 419, -1019, 1641, 1423, -863, 578, 14, 30, 442, 946,
  216, 1527, -1434, -839, -286, 108, 2298, 93, 910, -1443, -789, -366, 2981,
  -274, -197, 2222, -1245, -555, 1701, -1770, -1165, -134, -656, 1304, 233,
  -182, 2149, 683, 19, -2611, -1391, 744, 228, -908, -186, -285, -1040,
  2742, 810, 994, -769, -13, 984, -1381, 513, -330, 695, -1776, 3696, 1846,
  -880, 834, 1345, -1188, 547, 1444, 1511, 1365, 1702, -477, 599, 469, 2068,
  2189, -2331, -1061, -51, -109, 2262, -1661, -234, -1145, 59, 2382, 3122,
  2091, 572, 379, 1894, -1361, -352, 1572, 1282, 2139, -1183, -1531, -1096,
  111, -605, 801, -363, -507, -6, -626, -1856, 1769, 682, -567, 1783, 2172,
  1436, -900, 746, 604, 2266, 1409, -875, -700, 182, 2174, 517, 973, 282,
  -549, 1332, -1365, -986, -677, -3025, -834]

theorem fractionalNearFrameSubtreeG2R0606_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0606Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0606Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0606Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0606_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0606LowerBoundTable : List ℤ :=
  [454, 2081, 33, 317, 2364, 3190, 32, 216, 926, 13189, 1730, 1930, 5955,
  5666, 1414, 1471, 2940, 4169, 5509, 3836, 3663, 3299, 2262, -43, 4195]

def fractionalNearFrameSubtreeG2R0606LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0606Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0606LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
