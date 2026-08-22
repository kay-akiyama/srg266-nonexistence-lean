import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0594`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0594Mask : ℕ := 6866135128187682

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0594Witness : Array ℤ :=
  #[-704, -158, 79, -1458, 0, 83, -2312, -626, -59, 613, 603, 824, 0, 1737,
  454, 3230, 1960, 1465, 157, -136, -892, -2925, 2663, 2214, 0, 981, -627,
  -2498, -526, 319, 2633, 3041, 2743, -2455, 18, -151, 2420, 1436, -1994,
  -1428, -3704, 931, 2394, 2787, 3509, 3389, 2268, -492, 0, 400, -2589, 429,
  -4107, -2532, -1586, 2432, 2167, 737, 30, 448, 2080, 451, 2373, 1107,
  -501, -3093, -1741, -1297, -50, 2845, -590, -324, 1103, 1665, -1451, 387,
  22, -40, 1073, -433, -188, -413, 1487, 1183, 328, -800, 475, -1282, -667,
  -1810, 27, 1419, 2397, 491, -2746, 2008, -3128, 667, -1179, 1647, 182,
  1404, 1679, 1439, 768, 2551, -139, -1148, 1454, -293, -2277, 3024, 438,
  1853, 340, -1066, 90, 1405, 1448, -2995, 2951, -2223, -3616, -234, 302,
  -863, -371, 1045, 1483, 3842, 1318, 341, 2997, -3203, 1694, -1505, 1398,
  -2899, 908, 2341, -1074, 346, -1434, 2661, -1706, 3445, 945, 3195, 4505,
  -94, 754, 2042, 3372, 234, -690, 679, 1105, -859, 3020, -1798, 2348, 1796,
  2098, 1607, 789, 932, -1036, -213]

theorem fractionalNearFrameSubtreeG2R0594_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0594Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0594Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0594Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0594_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0594LowerBoundTable : List ℤ :=
  [2419, 7427, 5700, 4870, 1716, 5332, -42, 32, 5006, 14281, 4506, 8745,
  7316, 10337, 2630, 5811, 9061, -3191, 14181, -261, 13243, -911, 2772,
  -2109, 10677]

def fractionalNearFrameSubtreeG2R0594LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0594Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0594LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
