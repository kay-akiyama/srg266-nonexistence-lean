import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0109`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0109Mask : ℕ := 5385118295958154

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0109Witness : Array ℤ :=
  #[908, -205, 1354, 721, -723, 3259, -133, 287, 1303, 884, -404, -1755,
  -500, -751, 378, -5812, 602, -341, -4467, 802, 1092, -376, -2477, -1014,
  2446, -1224, 99, 1030, 8181, 130, -5966, -623, 1884, 421, 602, -3057, 285,
  845, 1338, 2686, -978, 4567, 2812, 1160, -717, -781, -2471, 1432, -700,
  -180, 1965, -480, 1238, -585, -2280, -5206, -5370, 2295, 3090, 1546, 0,
  2693, 2088, 3211, 2064, 1403, 1896, 1578, 723, -1998, 862, 680, -2455,
  614, 1390, -929, 7586, -1622, -106, 1886, -673, 399, 2240, -536, 59, 573,
  6425, -785, -432, 406, 194, 336, 14, 2554, 2004, 6965, -138, -219, 230,
  -1799, -751, -2086, 361, 82, -2079, 262, 45, 2256, -1429, -1792, 1913,
  -498, -734, -1191, 700, 1124, 2806, 1213, -11, -668, 2014, 980, 57, 3206,
  3444, -730, -4038, 1852, 2453, 324, -708, -1478, 1932, -646, -1710, 3365,
  922, 151, -3448, -1528, -2400, -1653, -1552, -728, 893, 1112, 4929, -2335,
  430, 1832, -369, -2622, 123, -6106, 6130, -1715, 422, -892, 294, -6716,
  -131, -498, 8400, 886, -2680, -1628, -7733, 1908]

theorem fractionalNearFrameSubtreeG3R0109_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0109Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0109Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0109Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0109_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0109LowerBoundTable : List ℤ :=
  [395, 33, 2829, 2609, 633, 32, 3534, 33, 3399, -3327, 1528, 4146, 1827,
  7106, 4383, 3999, 13172, 8509, 3199, 607, 5786, 4269, 3696, 6730, 1389]

def fractionalNearFrameSubtreeG3R0109LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0109Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0109LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
