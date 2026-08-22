import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0028`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0028Mask : ℕ := 1358769118216259

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0028Witness : Array ℤ :=
  #[924, -2082, 7641, 91, -515, -3359, 4752, -3387, -8031, -11050, -6394,
  -143, 2920, 3819, 3096, 2373, 2179, 1877, 4001, 5018, -1212, -2798, 4866,
  -732, -7232, -5718, -4423, 1609, -4084, 3560, 547, 0, 2483, 2195, 4606,
  2082, 429, -5789, -6607, 156, -6112, 3353, -2969, -737, -4379, 906, -292,
  356, -2921, 4476, 7802, 2473, 5376, -4704, -2079, -337, -1737, 360, 4881,
  1581, -15, 4864, 476, 2929, 16, -1674, 12475, 155, -5511, 3571, 4037,
  -2330, -4162, -2312, -5267, -2403, -3003, -5666, 33, 3239, -311, -4921,
  -243, -1142, -1695, -2083, -830, 3739, 2150, 8258, 2697, 2645, 4860,
  -3011, -1492, 4615, 1918, 4771, 1523, 2230, 4783, 5446, 7977, 1884, 2762,
  12186, -319, -1256, -4204, -7846, -7259, -4921, 8412, 6962, 166, -414,
  -7713, 827, 2247, 2427, 170, 5145, -1891, -6750, -10385, 9460, 2593,
  -8630, -7999, -949, 1397, 4213, 4680, -10498, 7603, 4913, 207, 9770, 2265,
  1632, 7954, 4989, 1328, 5108, 2192, 7047, 5377, 3209, 4406, 7004, 2260,
  2591, 1344, 1753, -4273, -3446, 10, 29, -1441, -1027, -3264, -2254, 2469,
  -2343, 273, -3887, -307, 1828]

theorem fractionalNearFrameSubtreeG5R0028_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0028Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0028Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0028Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0028_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0028LowerBoundTable : List ℤ :=
  [-508, 12142, 32, 10272, 4702, 2378, 4104, 7915, 7094, 4523, 237, 17764,
  22085, 3668, 11061, -5576, -8152, 16636, -5679, 23305, -4494, 13227, 100,
  10277, 11530]

def fractionalNearFrameSubtreeG5R0028LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0028Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0028LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
