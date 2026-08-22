import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0063`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0063Mask : ℕ := 954019093619850

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0063Witness : Array ℤ :=
  #[-1056, -881, 1599, -1486, 1430, -687, -629, 1986, 95, 1539, 0, 327, 365,
  982, -458, 17, 1811, 1198, 40, 42, -189, 926, -362, -873, -1143, -506,
  847, 1168, 1155, 2557, -480, 1938, 819, -86, 1259, -600, -491, 1392, -614,
  -346, 427, -1464, -1039, -2417, -300, 576, 1063, 1240, 1950, 962, 149,
  303, -830, 291, -1004, -707, -525, 322, -287, 2811, 65, 45, -1005, 0, -33,
  857, 0, -535, -1285, 1083, -1099, 880, -794, 3031, 2123, 370, 3279, 358,
  718, -723, 625, 1498, -627, -490, -259, 848, 493, -608, 26, 1257, -2601,
  -375, -1083, 264, -10, 181, 586, 617, -718, -365, 219, 907, 821, 63, -134,
  -165, 2031, 2387, -533, 2481, 1218, 331, 344, -113, -2306, -512, -2505,
  127, 1316, 476, 177, 483, 237, -522, 1669, -231, 464, 216, -1080, -1165,
  888, -1546, 506, 120, 625, -1508, -55, 1533, 1546, -450, 1324, 458, 1330,
  680, -129, -1095, 1152, 293, 394, -943, 281, -1307, 377, -261, -547, -697,
  1253, -1521, -2284, -1099, -583, 2583, 742, -45, -488, 605, -1385, -500]

theorem fractionalNearFrameSubtreeG2R0063_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0063Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0063Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0063Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0063_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0063LowerBoundTable : List ℤ :=
  [310, 1032, 32, 3283, 608, 552, -103, 2810, 4511, -1251, 814, 6689, 99,
  3598, -2008, 987, 4790, 4042, 100, 2718, 11575, 3568, 5275, 99, 5363]

def fractionalNearFrameSubtreeG2R0063LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0063Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0063LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
