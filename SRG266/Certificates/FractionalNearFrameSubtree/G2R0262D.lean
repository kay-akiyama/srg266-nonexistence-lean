import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0262`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0262Mask : ℕ := 5368611864167050

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0262Witness : Array ℤ :=
  #[-384, 2771, 2265, 1586, 1739, 1256, 801, -1874, 60, -3277, -806, -499,
  -1174, -317, 477, -528, -1958, -889, 195, 717, -180, 86, 541, 1237, 813,
  1245, 474, 1042, 420, -155, -34, 1431, 526, 550, 281, 680, 465, -481, 30,
  188, 1749, 1568, 599, -175, 74, 1883, 51, 1505, 2067, -951, 741, -1621,
  -971, -2847, 663, -296, 192, 714, -90, 1293, -688, -562, 964, 1534, -399,
  -386, 114, 915, 802, 1538, -843, -24, 2358, 293, 315, -85, 1655, 703, 312,
  585, 53, 74, 752, 185, 168, -984, 2333, -661, 1866, 454, -26, 21, -941,
  1112, 553, 574, 2154, -410, 766, 77, -2279, 598, 155, 863, 2317, -837,
  121, -2564, -637, -2462, -487, 747, -1202, -1470, 805, 563, -126, 794,
  -1610, -1704, -508, 962, 1351, 1550, 2510, -295, 1037, -2755, -154, 154,
  -788, 702, 0, 1528, 751, 394, -99, -396, 1315, 248, 96, -1664, 1251, -454,
  2543, 2584, -999, 985, -720, -2588, 1948, 762, -258, 835, 628, -758, 2652,
  1009, 694, -111, -400, -26, 415, 464, 1118, -175, 231, 1724]

theorem fractionalNearFrameSubtreeG2R0262_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0262Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0262Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0262Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0262_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0262LowerBoundTable : List ℤ :=
  [2127, 3321, 3127, 3992, 3921, 1378, 33, 3592, 1742, 904, -3182, 5740,
  5118, 3195, 245, 11571, 4243, 7907, 3227, 7871, 6853, 5031, 99, 2970,
  1768]

def fractionalNearFrameSubtreeG2R0262LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0262Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0262LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
