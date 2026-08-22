import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0012`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0012Mask : ℕ := 265977209479305

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0012Witness : Array ℤ :=
  #[807, -185, 1969, -2099, 5527, 263, -5686, -904, 5431, 0, -1080, -38,
  -3510, -2085, -4373, -1878, 750, 0, 841, -2027, -898, -3599, -154, 915,
  -2839, -132, 3417, 900, 3157, 1998, 3736, 4032, -1587, -1914, 2874, -1588,
  479, 0, 885, -501, -3069, -429, -2511, -555, -184, 2394, 3838, 2672,
  -2454, 1557, 2916, 975, 578, 515, 3460, 1682, -3335, 3619, 1757, 2159,
  -42, -164, 2629, 35, 823, 1679, -371, 1700, -4209, 2452, 1122, 359, 1426,
  116, 1991, 1708, -124, 5663, -2301, 2470, -1444, -8, -728, 1425, 2671,
  2756, 730, 4247, 2662, 3419, 564, -1517, 2518, 390, 474, -2409, -4111,
  3359, 3729, 2418, -285, -357, 479, 1573, -2141, -1732, -2739, -2413, 2653,
  -1289, -1898, -535, -1022, -5072, -1390, -2023, -2737, 1734, 1999, -310,
  2550, 3766, 3033, 4114, 1154, 1163, 3013, 821, 379, 156, -496, -4590,
  2363, -2324, -1215, -5435, -1278, 447, -1596, -315, 34, -47, 227, -957,
  4225, -156, 1772, -962, -1612, 910, 2226, 3449, -24, -492, 240, 2135, 474,
  -1484, 1418, -626, 1807, -636, 4138, -1479, 1833, 3566, 393, 1311]

theorem fractionalNearFrameSubtreeG1R0012_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0012Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0012Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0012Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0012_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0012LowerBoundTable : List ℤ :=
  [2043, 453, 9683, 8765, 9, 2069, -5018, 2949, 12298, 11773, -2603, 9773,
  12318, 99, 98, 6957, 14319, 5619, 3410, 8352, 12341, 100, 4952, 12627,
  -3887]

def fractionalNearFrameSubtreeG1R0012LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0012Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0012LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
