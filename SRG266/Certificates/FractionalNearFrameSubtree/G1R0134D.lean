import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0134`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0134Mask : ℕ := 1022437942266642

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0134Witness : Array ℤ :=
  #[-790, 8, 976, -140, 1865, 1487, -1330, 125, 215, 0, -1346, 0, -2000,
  -1424, -678, -22, -456, 0, 258, 305, 1662, -770, 1417, -273, 561, 711,
  1040, -531, -296, 1648, -824, -1353, -1219, -918, -934, 1699, 1144, 864,
  543, 423, -176, -208, -147, -1032, 98, 109, -714, 550, 1039, 1139, 659,
  863, -22, -173, -238, -310, -1299, 1664, 1096, -611, -308, -1080, 856,
  -1614, -737, -129, 896, 974, -541, 883, 705, 79, 211, -1024, 312, -492,
  -784, 1133, 657, 418, 389, 1406, 943, 254, 44, 1021, -228, -540, -534,
  507, 372, -873, -1025, -67, -729, -843, -1069, 481, -440, 850, 854, 997,
  409, 268, -399, -99, -1123, -202, -2048, -1555, 1491, 429, 108, 329, 760,
  629, -255, -639, -922, 692, 631, -725, -482, 518, -542, -1042, 286, -493,
  2006, 414, 804, 98, -381, -522, -25, -1125, 469, 181, 398, 375, -644,
  -262, 819, 687, 1109, -197, -181, 218, 612, 429, -328, 50, 709, 808, 689,
  7, 957, -659, 1225, 2166, -1970, 1156, 675, 1074, 693, 1113, -419, 1802]

theorem fractionalNearFrameSubtreeG1R0134_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0134Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0134Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0134Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0134_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0134LowerBoundTable : List ℤ :=
  [748, 2888, 686, 1034, 1901, 33, 2568, -691, -1234, 2961, 5189, 647, 1517,
  -2724, 1737, -1699, 100, 4378, 2804, 1022, 816, 4588, 4620, 2763, 1564]

def fractionalNearFrameSubtreeG1R0134LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0134Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0134LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
