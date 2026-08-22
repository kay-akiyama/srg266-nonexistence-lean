import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0020`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0020Mask : ℕ := 888054620985889

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0020Witness : Array ℤ :=
  #[4551, 4049, 4522, 6411, 3870, 1524, 1361, 886, 3991, -2462, 429, 668,
  -2819, -6466, 1770, -4785, -5005, -1093, 2116, -3789, -1403, -3203, -2689,
  2702, -6524, 2882, -227, -5377, 8728, 6621, 2773, 4221, -1540, -2320,
  -2233, -1029, 2541, 1380, 1572, -124, -2435, 3792, 2908, -2233, -628,
  2356, 399, 1255, -167, 2901, 2248, -3209, -2643, -793, 1650, 3307, 2162,
  1384, 1095, 2952, -1140, -3842, 1877, -1489, 62, 2863, 2800, -1428, 1571,
  3912, 942, 1803, 1922, 4159, -1612, -2825, -1962, 1553, 3747, 2084, 5397,
  4130, -7060, 1257, -4134, -4193, -101, -6326, -184, -4343, 1323, 5037,
  3198, 2146, 5787, 784, -3442, 802, 1911, 76, 1272, 4136, -1739, -3062,
  -100, 4554, -5292, -1050, -298, 2542, -2798, -4177, -1290, 3532, 3185,
  -4859, -5395, 146, 4986, -1531, -3696, 3961, 3472, 8061, 4152, -3307,
  -921, -3473, 2970, -6608, 2648, 4400, -4769, 4691, 6410, -1707, -7791,
  1387, 5668, 6002, -109, 2652, 6257, 2936, 3066, 7704, -1081, -4743, -2353,
  8917, 680, -3361, 465, -6963, -4699, 374, 7718, 1354, -7765, 2435, 7770,
  -6014, -3173, -3088, 204, -575, -2981, 9348]

theorem fractionalNearFrameSubtreeG3R0020_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0020Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0020Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0020Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0020_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0020LowerBoundTable : List ℤ :=
  [518, 3105, 33, 32, 14179, 31, 32, 10178, 9903, 3956, 5024, 10449, 8535,
  21385, -9859, 12814, -9117, 10204, -7038, -9272, 17171, 14485, 16205,
  22742, 18237]

def fractionalNearFrameSubtreeG3R0020LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0020Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0020LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
