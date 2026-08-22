import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0587`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0587Mask : ℕ := 6854996399461464

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0587Witness : Array ℤ :=
  #[-280, 867, -1028, -78, 552, -197, 696, -153, -474, 902, -950, -860, 99,
  1094, -602, 237, -773, 875, -113, 1463, 145, 546, 1710, 1327, -2211,
  -1774, -486, -388, -525, -1827, 2287, -113, 1000, -2005, 1014, -353, 2538,
  -836, -1952, -1552, 277, 676, 906, -84, -937, 2155, -936, -224, -3945,
  -124, 467, -84, 2386, -499, -1673, 1849, -604, -1319, 1333, -984, 637,
  533, -2294, 525, -663, 1197, -156, -1371, -39, 1777, -1136, -450, 251,
  -821, -1183, -606, 421, 617, 2750, -412, -878, 720, 290, -4292, 2458,
  -1500, -277, 229, 542, 2641, 273, 135, -1241, 744, -40, -373, -2737, 1335,
  -486, -1251, 563, 2997, 275, -88, 1596, -1569, 1400, 2289, 4834, -1545,
  -1274, -2867, 372, 862, 1127, 1357, -1733, -940, -54, 191, 1704, 1165,
  305, 131, -1534, -1389, 593, 739, 2026, 1430, 543, -351, -1034, -1687,
  579, 323, -291, 3340, -102, 1609, -2671, 2572, -1584, 1550, -2384, 313,
  809, 794, -928, 1555, -546, 350, -2528, 425, -1482, 93, 2084, -81, 954,
  664, -777, -954, 0, -1230, 3032, 2182, -67, 289]

theorem fractionalNearFrameSubtreeG2R0587_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0587Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0587Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0587Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0587_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0587LowerBoundTable : List ℤ :=
  [-460, 2891, 1159, 1944, 1749, 1200, 558, 31, -2621, 5412, 1359, -4727,
  1032, 3901, 811, 1136, -8753, 2649, 1109, 7810, 2897, -2091, 99, 100,
  2417]

def fractionalNearFrameSubtreeG2R0587LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0587Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0587LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
