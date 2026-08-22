import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G4R0017`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0017Mask : ℕ := 4884693992026373

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0017Witness : Array ℤ :=
  #[-454, -2477, 826, -421, -1221, -2315, -1172, 768, -1943, -117, 366,
  2439, 2671, 3924, -19, 0, 702, 2372, -1016, 1791, 509, -1071, 472, 475,
  1402, 581, 3807, -3390, -2083, -4422, -1275, -1225, -1142, 65, -1046,
  -3404, 2613, -39, -5532, 245, 3114, 1311, 3157, 383, -912, 917, -155,
  -945, 2391, 1014, 565, -5821, -1401, 1630, 854, 0, -983, 1496, -3518,
  -2317, -980, 269, -1750, 379, 797, -224, 394, 2824, 3417, 715, -1463,
  4134, 925, -2085, 917, 361, 770, -16, 171, -1040, -539, 550, -1101, 2848,
  822, -210, 1073, 1037, -186, -2495, 514, -2574, -802, -3486, 1361, -1937,
  825, 1017, 1123, 18, -650, 542, 299, 158, -2016, 3322, 790, 124, 905,
  1043, 2241, -463, -1134, -146, 402, 93, 755, 1102, 1671, 1446, 2904, -147,
  2270, 2651, 251, -340, 2504, -231, -1048, -810, 1838, 678, 492, 1181,
  2503, 2119, -590, 1416, 593, 4015, 2185, 2369, -2046, -1278, 2930, -1676,
  1418, 2651, -1219, -679, -1416, -196, 157, 751, 983, -626, -286, -329,
  -67, 422, 151, -1841, -1360, 2137, 1703, 1464, 432, 183]

theorem fractionalNearFrameSubtreeG4R0017_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0017Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0017Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0017Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0017_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0017LowerBoundTable : List ℤ :=
  [303, 4442, 3925, 2286, 3229, 31, 2564, 32, 1637, 5676, 3596, 10448, 5758,
  6364, 3115, 4498, 8563, 5815, 479, 100, -5114, 2596, 1662, 2154, 2641]

def fractionalNearFrameSubtreeG4R0017LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0017Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0017LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
