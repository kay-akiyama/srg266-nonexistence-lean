import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0227`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0227Mask : ℕ := 2496462243401968

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0227Witness : Array ℤ :=
  #[-1122, -173, 430, 2216, 919, -3385, -1137, -120, -1420, -2054, 1873,
  2364, 788, 1836, 564, 381, 151, 552, -901, 801, 2587, 234, 2427, 1736,
  -1870, 1187, -2000, -2934, 706, -996, -542, -1772, 478, -304, -992, -678,
  -931, 2908, 1712, 1295, 928, 2135, -1366, -2575, -2526, 361, 2845, 1125,
  1275, -266, 2611, 878, 158, 2295, -1265, -1135, 1598, -213, -531, 1736,
  536, 452, 2271, -255, 3675, -2220, 3660, -176, 883, -259, -1280, 1285,
  262, 1928, -385, -332, 2009, 1938, 967, 52, 1923, -431, 1289, 1562, -2571,
  -1959, 2277, -574, 91, 3210, 999, 1800, 760, -74, 2050, -2334, 1529, 493,
  3947, 1159, 247, 2197, 923, 2539, -1174, 1575, -117, -1872, 553, 1895,
  -1048, 208, 2587, 336, 3488, -332, 2420, 1598, -1654, 1338, 1118, 1038,
  -2221, -2912, -344, 738, 227, 1005, -116, 3244, 1869, 2223, 313, -1700,
  481, 1259, 376, 1045, -3228, -53, 574, -136, 652, -1875, -372, 661, 466,
  1737, -1578, 1182, -227, -669, 2174, 427, 1135, -53, 451, -354, -217,
  -661, 950, -386, -750, -352, -667, 822, -2526, 2003]

theorem fractionalNearFrameSubtreeG2R0227_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0227Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0227Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0227Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0227_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0227LowerBoundTable : List ℤ :=
  [3708, 2024, 4310, 6172, 4705, 4711, 4016, 3790, 2748, -203, 8928, 8381,
  -1103, 4216, 1716, 3105, 6662, 11560, 10315, 5884, 6994, 9607, 9223, 100,
  5169]

def fractionalNearFrameSubtreeG2R0227LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0227Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0227LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
