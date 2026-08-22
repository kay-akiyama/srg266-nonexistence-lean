import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0022`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0022Mask : ℕ := 900899056032785

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0022Witness : Array ℤ :=
  #[340, 1285, 2088, 1060, 1422, 204, 89, -452, -616, -130, 0, 111, 381,
  -695, -811, -1056, -282, -283, -1200, -916, 413, 276, -1098, 196, 777,
  932, 578, 773, -102, -159, 221, 855, -2073, -609, -463, -1245, 94, 513,
  729, 454, 772, 296, 353, 132, 1270, -1397, -1554, 670, 342, 668, 1539,
  1380, -97, 2627, 780, -246, -791, -1, 498, 310, 287, -1194, 864, 1585,
  -465, -276, 408, -152, 431, -468, 17, 415, -265, 654, -888, -369, -1828,
  1511, 14, -493, 1789, -221, 199, 457, -160, -733, 533, 1422, 101, -735,
  1005, 539, 722, -363, 951, 1360, 105, 206, -461, 130, 373, 649, -893,
  -895, 138, 910, 1317, -370, 139, 1105, -310, 719, -336, -380, -93, 717,
  821, -762, 61, -1150, 562, 874, 384, 1220, -272, -871, -1375, -887, 178,
  -100, -124, -934, 809, 0, 0, 96, -703, -669, 847, -268, 79, -436, -1018,
  327, 284, 556, -762, 403, -166, 437, 461, 671, 647, 287, -70, 28, 724,
  -85, 997, 588, 15, 496, 913, 0, 945, 351, 1020, -339]

theorem fractionalNearFrameSubtreeG3R0022_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0022Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0022Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0022Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0022_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0022LowerBoundTable : List ℤ :=
  [358, 2095, 1562, 901, 32, 1879, 33, 2851, 2972, 1457, 1282, 2519, 3498,
  -545, 101, 2232, 4272, -382, 3296, 4517, 2343, 4648, 100, 437, 5731]

def fractionalNearFrameSubtreeG3R0022LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0022Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0022LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
