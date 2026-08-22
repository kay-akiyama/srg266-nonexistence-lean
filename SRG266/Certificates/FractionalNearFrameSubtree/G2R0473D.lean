import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0473`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0473Mask : ℕ := 5809429561117784

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0473Witness : Array ℤ :=
  #[355, -1851, 1717, -1828, -1846, 1841, -94, -2158, 183, -2339, 3313,
  3749, 1378, 548, 2902, 498, 3819, 799, 1273, 644, 828, 1984, -348, -618,
  -2666, -2521, -3920, -2980, 730, 770, 1526, 1025, -730, 3961, 1063, 772,
  -1023, 1446, 1745, 1, -94, -2596, 1295, -239, 318, -420, 1943, 1158, 3608,
  -136, -180, 235, 853, -125, 3885, 4008, 0, 1541, 84, -1015, -1953, -870,
  508, -2615, -831, -508, -2407, 1154, 2932, -305, 89, -163, -767, 806,
  1318, -1374, 3058, 181, -97, -237, -642, -94, 906, 39, 2112, -748, -1047,
  -1841, -1077, -17, -1363, 723, 572, 315, -744, -1591, -547, -1384, 1109,
  -208, 1152, -2433, -293, 513, -524, -912, 1086, 917, -1441, 310, 794, 627,
  -1935, -2584, 1896, 0, -611, 1210, -2232, 949, 2863, 681, 1556, -4137,
  -1055, -1437, 2853, -883, 2628, 1414, -4328, -825, 1717, 2147, -652, 3450,
  3087, 727, 7, 1340, 1638, 2217, -317, -871, 2457, 997, 3902, -723, 790,
  -134, 2280, 1658, 3086, 1978, 585, 746, 1436, -788, 2272, 2629, 94, 458,
  1029, -1101, 2581, 1925, 3129, 2209]

theorem fractionalNearFrameSubtreeG2R0473_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0473Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0473Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0473Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0473_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0473LowerBoundTable : List ℤ :=
  [3539, 8111, 6363, 3832, 2035, 2919, 3020, 4123, 6584, 16855, 4404, 5558,
  6723, 4255, 10419, -2582, 7435, 101, 68, -276, 3188, 2963, 3959, 8561,
  2150]

def fractionalNearFrameSubtreeG2R0473LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0473Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0473LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
