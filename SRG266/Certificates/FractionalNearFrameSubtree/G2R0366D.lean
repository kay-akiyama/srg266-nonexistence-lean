import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0366`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0366Mask : ℕ := 5715933355259148

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0366Witness : Array ℤ :=
  #[334, -813, -372, -2424, -1480, 60, 961, 1796, 99, 235, 0, 289, 1667, 78,
  733, 1519, -390, -1341, 824, -322, -51, 588, 917, 2830, 183, 918, 18,
  -165, -152, -213, -287, 1581, 1595, 1245, 544, 1164, -1156, -2128, 296,
  -279, 1002, 1180, -1358, -1241, -1041, -1195, -2756, -464, -329, -205,
  2193, 1005, 2487, -1134, 363, -1072, 2439, -327, -367, 270, 482, -42,
  1004, 889, 386, 250, 780, 462, 733, -2139, 743, 400, 938, 393, 1872, 1510,
  766, 2180, 2051, 1014, 1540, 1417, -554, -975, 289, -476, -1074, 1222,
  -21, -34, -1079, -1410, 153, 486, 28, 754, -117, -194, 790, -21, -919,
  -577, -1107, 1067, -310, 1163, 1554, 171, 149, 1227, 1744, 69, -292, 455,
  -1165, 906, 369, -966, 845, 1060, -635, -238, 620, -742, 2985, 3527, -434,
  -500, -1545, -167, -10, -322, -943, 338, 899, -268, 861, -222, -141, 82,
  -1812, 176, 606, 635, -1467, 236, -47, -1029, 274, -1330, 740, 0, 618,
  -1478, -847, 110, 1085, -141, -732, 466, -426, 0, -1048, -992, 275, 5,
  271, -432]

theorem fractionalNearFrameSubtreeG2R0366_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0366Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0366Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0366Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0366_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0366LowerBoundTable : List ℤ :=
  [1183, -652, 1754, 1458, 534, 3669, 91, 813, 3901, 3770, -1938, 99, 1776,
  6910, 3893, 880, 6216, -1478, 3321, 890, 5373, 4036, 5568, -580, 3706]

def fractionalNearFrameSubtreeG2R0366LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0366Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0366LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
