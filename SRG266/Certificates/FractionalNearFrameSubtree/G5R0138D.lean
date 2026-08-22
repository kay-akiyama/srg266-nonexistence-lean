import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0138`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0138Mask : ℕ := 6104747621197090

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0138Witness : Array ℤ :=
  #[-571, -1665, -367, 2199, -1443, 990, 6409, 2877, 562, 3419, 6690, -7264,
  -3752, -2001, -2451, -2181, 45, 1261, 1789, 591, -1687, -909, 3182, -2759,
  -2704, -745, 3215, 1349, 1529, 3851, 2467, 597, 3382, -1419, -3551, -752,
  2432, 1306, 2572, -2541, 0, 352, 1998, 676, 1430, -1762, -138, 907, 385,
  1396, -411, 6480, 379, 2908, 1841, 3118, 1155, 705, -4374, -5652, -3733,
  2905, -1529, 403, 1590, 760, -1482, 75, -254, 341, 2009, -522, -1440,
  -2892, -685, -250, 1469, -3662, -2002, 2328, 1924, 1196, 323, 1891, 75,
  714, -935, 1859, 237, 930, -2575, 1460, 1486, 71, 1820, 2973, -67, -3717,
  3171, -207, -1610, 3460, -2247, 691, 473, 2793, 627, -1320, 5348, 1560,
  2352, 4822, 2702, 8589, -4846, -2383, -1208, -3035, 4271, -540, 365, 0,
  7963, 2098, 733, 2697, -201, -1527, -2623, -1972, 832, 2215, 814, 1567,
  210, 123, -860, 4189, 4031, -2695, -3615, 410, 148, 740, -412, -3404,
  -147, -214, 3222, 1542, -3223, 4167, 3614, -3563, 2850, -1409, 1453,
  -2980, 2497, 1191, -54, 4127, 4509, 3460, 2220, -568, 657, -1873]

theorem fractionalNearFrameSubtreeG5R0138_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0138Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0138Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0138Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0138_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0138LowerBoundTable : List ℤ :=
  [4505, 9213, 10238, 31, 3077, 2221, 9372, 4235, 5441, 6625, 28642, 7853,
  16442, 3714, 8205, 6327, 13581, -6175, 8759, 2693, -5905, 11199, 928,
  4813, 5470]

def fractionalNearFrameSubtreeG5R0138LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0138Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0138LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
