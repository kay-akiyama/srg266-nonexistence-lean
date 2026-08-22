import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0266`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0266Mask : ℕ := 5369776135934168

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0266Witness : Array ℤ :=
  #[-462, 224, -692, 587, -564, -29, 1382, 867, 217, 61, 343, -95, -626,
  -179, 1461, 1365, 802, 54, -228, 252, 553, -309, 471, -787, 1262, 637,
  -521, -495, 781, -412, -812, 1074, 1177, 315, -986, -471, -542, 269, 1894,
  3, 15, -351, 312, -190, 503, 1157, -554, -32, 285, 172, -359, -514, -225,
  934, -70, 827, -41, 0, 526, -479, -456, 769, -825, -569, 1134, -1014,
  -465, 994, -16, -473, 641, 2226, -169, 562, 477, -1103, 411, -284, 745,
  139, 132, 438, 99, -258, 1364, -353, 779, 622, 987, -275, -268, -128, 36,
  -185, -159, 243, -851, 1334, 1259, 158, 316, 605, 906, -279, -817, 390,
  -641, -6, -302, 10, 412, -570, 243, 530, 1047, 1301, 687, 60, 1317, 131,
  -1413, 330, -503, -440, 343, -209, 284, 501, -547, -392, 444, -543, 544,
  957, -532, 298, -708, 973, -28, -794, -79, 1319, 68, -545, 1005, 784, 253,
  98, -618, 1149, 625, -482, -1211, 678, -160, 213, 231, 492, -369, -917,
  282, -630, -248, -152, -800, -31, 957, 54]

theorem fractionalNearFrameSubtreeG2R0266_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0266Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0266Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0266Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0266_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0266LowerBoundTable : List ℤ :=
  [1286, 778, 1364, 1245, 1898, 905, 3934, 1411, 2331, 1206, 101, 2662,
  -1077, 441, 5199, 100, 100, 1167, 1656, 3637, -775, 1273, 4262, 5380,
  1748]

def fractionalNearFrameSubtreeG2R0266LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0266Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0266LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
