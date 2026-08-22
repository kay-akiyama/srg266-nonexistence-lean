import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0278`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0278Mask : ℕ := 5372868688450148

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0278Witness : Array ℤ :=
  #[479, -1264, 1487, 749, 481, -119, -464, 581, -1900, 13, -1949, 398, 617,
  243, 0, 788, 130, -2300, 742, 63, -1072, 0, -587, 569, -1918, 400, 1424,
  465, 2052, 1953, 81, 437, 61, 1086, 322, -84, 184, 97, 340, 647, 218,
  1082, -342, -1756, 559, 466, 122, 33, 31, -164, 28, 369, 1343, 194, 1292,
  811, 1442, 2063, 704, 997, -703, 152, 134, -604, -1268, -683, -506, 1517,
  1266, 276, -576, -78, -773, -602, -1447, 2406, 410, -1353, 73, -248, -574,
  187, 26, -212, -91, 1811, 851, -1619, 1039, 109, -279, -1089, -311, 2848,
  443, -1281, -215, -1464, -4, -1053, -870, 975, 198, 59, -802, -2147, 978,
  -1860, -459, 409, -506, 627, 1944, -245, 69, 2350, -108, -196, 594, 1164,
  306, -520, -1175, -1419, 865, 864, -427, 1007, -886, -1651, 1695, 859,
  1085, 1224, -65, 85, 1235, 279, 1966, -2373, -1727, 208, 599, -94, 363,
  -12, 1389, 1755, 839, 271, 1983, 1747, 614, -634, -1680, -1357, 776, -133,
  -1794, -1477, -13, -701, 665, 546, 993, -678, -2087, 259]

theorem fractionalNearFrameSubtreeG2R0278_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0278Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0278Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0278Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0278_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0278LowerBoundTable : List ℤ :=
  [893, 461, 33, 1731, 33, 2702, 33, 3807, 1735, 2756, 5404, 2800, 99, 2246,
  566, -3188, 2171, -1854, 2194, 100, 1345, -1899, 56, 101, 6345]

def fractionalNearFrameSubtreeG2R0278LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0278Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0278LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
