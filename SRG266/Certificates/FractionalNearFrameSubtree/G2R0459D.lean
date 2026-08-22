import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0459`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0459Mask : ℕ := 5807291636585098

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0459Witness : Array ℤ :=
  #[72, -2557, 801, -956, -873, -2819, -702, 850, 1519, -91, 2498, 210,
  1152, 411, 67, 707, 1818, -1755, 2068, 897, -1995, 204, 165, 661, 720,
  -308, -98, 1459, -455, 1677, 2534, 1992, -747, 438, -635, 476, -1168,
  2013, -133, 1768, 7, -1742, -1398, 408, -1645, -389, 140, -1230, 2485,
  -336, 2256, 1931, 1678, 2569, 3009, 1323, -1963, 560, -661, 88, -856, 400,
  -1578, 1338, -563, 1357, 1457, 559, 477, 959, -549, -193, -670, -88, -983,
  -1032, -1445, 1054, 858, 175, 1378, -1101, 1709, 1105, 535, -531, -648,
  -321, 1363, 286, 1260, 609, 1326, -550, 1973, -390, -229, 161, 1117, 2009,
  1213, 646, 1380, 1964, 2804, 1919, -31, -673, 1142, -328, 218, 399, 172,
  1790, 2216, 458, 1228, 1361, 1503, 59, 695, 424, -224, -432, 61, -586,
  -456, -566, 752, 653, 3332, -998, -876, 634, -73, 1011, -75, 1979, -256,
  2164, 110, 1408, -343, 874, 1864, 2272, -607, -1373, -1220, -382, 354, 43,
  2355, -1556, -2941, 1968, -1745, -268, 95, -350, 1754, 279, -565, -887,
  -126, 432, -1304, 332]

theorem fractionalNearFrameSubtreeG2R0459_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0459Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0459Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0459Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0459_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0459LowerBoundTable : List ℤ :=
  [3305, 3701, 4868, 6756, 3625, -920, 1619, 5178, 4199, 4811, 6439, 862,
  1105, 9010, 11245, 5672, 4105, 8388, 2541, 6765, 9662, -1676, 5444, 99,
  4448]

def fractionalNearFrameSubtreeG2R0459LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0459Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0459LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
