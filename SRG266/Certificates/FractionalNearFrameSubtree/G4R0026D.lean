import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G4R0026`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0026Mask : ℕ := 5363196768143633

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0026Witness : Array ℤ :=
  #[2791, 3128, 615, -1742, 308, 2577, 3683, 447, 1026, 6640, 3078, -1359,
  -4331, -4295, -5924, -2228, 3799, 1574, 2377, 3281, 86, -2533, 480, -2389,
  -6231, 2005, 824, 1744, 411, 835, 2537, 3402, 1309, 1096, 2491, 1, 677,
  -2956, 609, 1181, -5428, -2313, 350, 1587, -597, 3728, 4840, -2723, -1184,
  -2474, 5493, 1209, 1726, 276, 2728, 1389, 1209, 3336, -2726, 2735, 1105,
  119, -1577, 3727, -1811, 538, 3987, 4629, 891, 1627, -4310, -1444, -1522,
  5178, -5, 565, 1985, 1219, 6089, 1525, 1398, -795, 3127, -1199, 4238,
  -253, -126, -463, 1690, 5170, -1947, 1518, 3944, 4308, 631, -215, -1138,
  3109, 5771, 918, 294, -613, 628, -1175, -14, -803, 203, -3480, -2971,
  6798, 527, 2198, -2974, -1551, -1462, -5073, -939, -2220, 3654, -672,
  -2435, -1942, 3445, 2629, 1442, 1297, -2145, -3447, 2755, 2054, -3245,
  647, 7273, 3552, 3898, 1056, 967, 216, 2124, -3136, 2672, -166, -6697, 0,
  -21, -2823, -825, 169, 1179, 2388, 3055, 1332, -4178, -918, -569, 3743,
  -3045, 5943, 621, 539, 1299, 2420, 2084, 0, -3540, 314, 8130, 574]

theorem fractionalNearFrameSubtreeG4R0026_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0026Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0026Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0026Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0026_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0026LowerBoundTable : List ℤ :=
  [5861, 4554, 9190, 12152, 1805, 7403, 3255, 7644, 10734, 1862, 2429, 99,
  6332, 14124, 18553, 8411, 22355, 8143, -5968, 14000, 10220, 2681, 5824,
  13916, 14051]

def fractionalNearFrameSubtreeG4R0026LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0026Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0026LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
