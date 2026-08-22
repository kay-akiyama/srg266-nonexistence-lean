import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0174`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0174Mask : ℕ := 6863963745586706

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0174Witness : Array ℤ :=
  #[-2418, -1393, 451, 583, -86, 353, -1198, -653, 0, 1889, 1948, -1027,
  2401, 258, 1878, 1158, 1774, -901, 2389, 3792, 981, -1881, -2019, -2371,
  -1949, 63, -1755, 1991, -3175, 1683, 2720, -648, 3920, -832, 1728, -52,
  -81, -1139, -1573, 405, 4055, -5635, -350, -1577, 54, -779, -379, -508,
  1780, 2161, 4701, -2220, -2487, 2824, 3157, 2633, -1380, -2410, 5866, 446,
  -594, 4525, 896, -4553, 2887, -1935, 1022, 5657, -2308, -2668, -1405,
  2036, 2296, -1050, 3557, 975, -1277, -448, -254, -4182, -934, -1268, 547,
  3357, -2055, -11, 2334, 990, 381, -2926, -1754, -2890, -1210, 2563, -3279,
  2128, 793, 1307, 1481, -1495, -2747, -500, 1515, 3996, -2241, -721, -2290,
  1927, 1070, 1294, 3450, -458, -1402, 0, -4011, -2483, -1257, 935, 1999,
  1409, -2783, 1443, 0, -1422, 800, 1356, -1567, 1840, 0, -1126, -560,
  -1811, -110, 698, 94, 2972, -2233, 3196, 2303, -25, 300, 2656, 1992, 3393,
  -1310, -1071, -1910, 596, 995, 3569, -3238, -330, -233, 143, -1047, 784,
  2187, 2617, -4152, -836, -346, 5505, -1847, 246, -4125, 3575, 245, -801]

theorem fractionalNearFrameSubtreeG3R0174_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0174Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0174Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0174Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0174_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0174LowerBoundTable : List ℤ :=
  [-1724, 2711, -1770, 4666, 1919, -2606, 1828, 3099, 32, -6388, 5375, 3402,
  3355, 2662, 3891, -5619, 6512, -353, 8411, 7546, 6065, -427, 9506, 6299,
  13385]

def fractionalNearFrameSubtreeG3R0174LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0174Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0174LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
