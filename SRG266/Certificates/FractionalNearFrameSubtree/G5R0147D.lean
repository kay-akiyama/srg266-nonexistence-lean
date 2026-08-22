import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0147`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0147Mask : ℕ := 7976168039844208

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0147Witness : Array ℤ :=
  #[881, 633, -799, -1543, -164, -39, -1044, 566, -394, 96, 505, 3267, 545,
  900, 1494, 530, 608, 12, -1114, 1385, 279, 676, 507, 1148, -2474, -1332,
  -830, -1849, 990, -710, -54, 1084, -388, 48, 1019, 301, -886, -643, -1272,
  -325, 316, 1754, 54, 768, -824, 156, 1109, -959, 1074, 172, 1486, -1290,
  -831, -795, -150, 692, 570, 512, -398, 1332, -2737, 557, 267, 1281, -496,
  639, -136, -210, 214, 222, -965, 849, 558, -295, -2147, 331, 729, 783,
  1138, -1982, -6, 1490, 397, -483, 1393, 132, 368, -97, 349, -167, 2228,
  1172, -198, 721, 643, -376, -1392, -995, 66, -2334, -533, -341, -42, 130,
  -1369, 188, 1586, -551, -331, 87, 946, -1024, 220, -2286, 495, 947, 2080,
  232, 190, 880, 588, -334, 836, 296, 666, -1307, -1122, -505, 1007, -2127,
  390, 488, 1382, -365, 664, 2431, -252, -915, -234, -183, -2034, 970, -176,
  -332, -293, 2485, -892, 658, 264, -323, 572, -234, 604, 927, -939, 90,
  -1242, 1608, 876, -2413, -3382, 1326, -598, -827, 137, 1240, 916, -550]

theorem fractionalNearFrameSubtreeG5R0147_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0147Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0147Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0147Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0147_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0147LowerBoundTable : List ℤ :=
  [-710, 32, -507, 505, 1613, 33, 1261, 33, 1023, -974, 100, 100, 2065,
  1792, 2644, -2496, -320, 758, 333, -254, 4487, 3019, 3118, 3241, 2763]

def fractionalNearFrameSubtreeG5R0147LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0147Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0147LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
