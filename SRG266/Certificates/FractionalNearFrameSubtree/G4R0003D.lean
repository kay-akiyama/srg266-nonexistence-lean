import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G4R0003`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0003Mask : ℕ := 538377143156803

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0003Witness : Array ℤ :=
  #[751, 1472, 2076, -3288, -2045, -1646, 0, 1586, 1077, -1573, 103, 392,
  2477, -34, -1703, -692, 378, 41, -144, -979, -1084, -234, -953, 373,
  -1569, -124, -1388, 323, -914, 0, -56, 279, 136, -251, 240, -1674, -495,
  -1189, 151, 1304, 502, -527, -747, -272, -659, -62, -1243, 356, -262,
  1216, -737, -1039, 410, 1406, 873, -162, -1334, -88, 1258, 1200, 629,
  -1423, -1191, 1053, -994, -1404, -1211, 2267, 1726, 1446, 145, -1678, 770,
  426, -2168, -1013, -872, 1339, 518, 1533, 1199, 1171, 1892, 2054, 2094,
  1656, 261, -197, 1234, 614, 1641, 1841, -1193, 780, 805, 1538, 934, 1677,
  878, 1071, 24, 343, -844, 1055, 921, -3501, -621, -1926, -729, -2000,
  1463, -904, 32, 1537, 1906, 2864, -2385, -247, 1307, -2469, -669, 1306,
  1601, -1869, 474, -644, -272, 2600, -891, -1541, -824, -241, -563, -216,
  -3103, -2701, 68, -156, 16, 4173, -1660, -866, -106, 1533, 4233, -737,
  909, 2064, -258, 3626, 3952, -336, 239, -1271, -1654, -1661, -1718, 234,
  1160, -2287, -3460, -916, -883, -822, 1946, -741, 1516, -1824]

theorem fractionalNearFrameSubtreeG4R0003_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0003Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0003Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0003Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0003_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0003LowerBoundTable : List ℤ :=
  [-1719, 32, -2396, -2949, 6329, 1325, 2357, 2232, -1852, 4180, 1268, 101,
  -5255, 7709, -2891, 101, -3418, -1121, -1199, -1547, 100, -2181, 2224,
  1518, 9838]

def fractionalNearFrameSubtreeG4R0003LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0003Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0003LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
