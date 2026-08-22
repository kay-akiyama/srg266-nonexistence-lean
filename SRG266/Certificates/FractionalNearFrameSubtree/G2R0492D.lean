import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0492`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0492Mask : ℕ := 5811291175441172

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0492Witness : Array ℤ :=
  #[987, 0, -1401, -1003, -1290, -110, 877, 283, -136, -228, -456, 1065,
  738, 816, 577, -392, 1329, 294, 810, -598, 351, -137, 928, 439, 474, -271,
  -524, -609, -1374, -865, 755, 2075, 1029, -1109, -725, -1483, -374, -443,
  1119, -357, 1305, 153, -604, -1141, -177, 894, -327, 701, -203, 297, 477,
  -899, 869, 551, 623, 249, 785, -199, -729, 1231, -1147, 780, 1048, -1289,
  -757, 1065, 176, 2031, -936, 1902, 1483, -524, 881, -1306, -603, -264,
  460, -942, -710, -54, 169, -24, 227, 1117, 1085, 1333, -101, 1211, 369,
  -834, 643, -349, 28, -289, -663, -261, -1030, 662, 372, 720, 976, 698,
  386, 147, -921, 489, 436, 315, -965, -1679, -1041, -807, -450, 1745, 903,
  -457, 1035, -49, -496, -364, -107, -764, -394, -357, -274, -93, 256, 529,
  -733, -363, -558, 106, 31, 440, -607, -927, -99, 940, -89, -259, 630, 587,
  538, 975, -1089, 782, 314, 763, 295, 744, 616, -369, -122, 105, 69, 322,
  736, 492, 364, -428, 473, -317, -167, -128, 83, 800, 891, 655]

theorem fractionalNearFrameSubtreeG2R0492_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0492Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0492Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0492Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0492_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0492LowerBoundTable : List ℤ :=
  [362, 1289, 2454, -1126, 2847, 31, 956, 1410, 972, 841, 100, 100, 734,
  2553, -178, 660, 2500, 101, 1928, 100, 247, 4105, 1701, 3501, 3344]

def fractionalNearFrameSubtreeG2R0492LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0492Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0492LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
