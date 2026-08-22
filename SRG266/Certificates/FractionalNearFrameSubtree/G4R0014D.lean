import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G4R0014`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0014Mask : ℕ := 4871584208249093

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0014Witness : Array ℤ :=
  #[1462, 428, -54, -297, -161, 199, 90, -1367, 148, 910, -21, 637, 457,
  -913, -1127, -317, 75, 2390, 542, 0, 136, 250, -14, -1252, 483, 489, -124,
  -1693, -995, 83, -377, 83, 2277, 511, 562, 697, -367, 145, 87, 375, -483,
  -380, -993, -151, -725, 1932, 1649, 161, 359, -1007, -1780, 50, -79,
  -1050, -2350, 872, 837, -1378, 289, 181, -548, 1042, -628, -347, 1437,
  405, -396, 1612, -515, 404, -155, 339, 414, -312, -1712, -1042, 1026,
  -248, 305, -116, 468, -450, -354, 308, -978, 205, 217, 408, 435, 86, 225,
  -894, 0, 1892, 527, -937, 1010, -99, 196, -59, -794, -543, 1741, 1277,
  108, -730, 886, 868, 758, 275, -510, -1380, -561, -120, 600, 568, -1643,
  -2, 142, -367, -492, -53, 1054, 735, 303, 16, -24, -1241, -1057, -5, -875,
  1237, 1557, 1797, 331, 1276, 1657, 724, 21, 1074, 518, 789, -397, 0, 1084,
  386, -1126, -325, 267, 1549, 1632, -181, -60, 408, -528, -1306, 277, -827,
  -63, -282, -280, -1756, -781, -667, -1487, -122, 597, -64]

theorem fractionalNearFrameSubtreeG4R0014_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0014Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0014Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0014Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0014_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0014LowerBoundTable : List ℤ :=
  [140, 32, -1062, 1954, 230, 1494, 21, -40, 208, 3530, 4720, -1214, -78,
  2672, 3027, -2539, 101, 1577, 954, 5634, 2060, -1761, 140, 4079, -995]

def fractionalNearFrameSubtreeG4R0014LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0014Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0014LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
