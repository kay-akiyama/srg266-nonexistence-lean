import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0126`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0126Mask : ℕ := 5862975896224070

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0126Witness : Array ℤ :=
  #[221, 606, 2899, 73, 1408, 129, 155, 0, 58, -387, -446, -2211, -1162,
  -117, -1711, 10, -924, -381, -245, -341, -1255, -141, -363, 550, 887,
  1696, -893, 716, 222, -694, -895, 25, -550, 2867, -139, 1114, -186, -455,
  -708, -361, -36, -319, -2571, 285, 1433, 318, 1327, 578, 1953, -106, 423,
  393, -41, 632, 1238, -2337, 3, -2743, 351, 511, 42, -514, 32, -32, 577,
  -188, -333, -981, 1977, -1811, -365, -1449, -2017, 1013, -531, -1493,
  -788, 2496, -2317, 484, 672, 222, 286, -79, 451, -652, 498, 600, -2562,
  306, -853, -1387, -196, -894, 1636, 1345, 584, -38, -1128, -359, -1067,
  559, 2708, 430, 1346, 2555, 446, 991, 1092, -120, -393, 894, -3651, 553,
  -2167, 1057, 1999, 584, 224, -3275, -742, 410, 775, 670, 259, 1398, 1426,
  924, -88, -1300, 469, 254, -513, 1352, -1203, -2127, 3555, -79, 295, -943,
  -1303, 1066, -3, -34, -53, -2474, 1213, 2903, 831, 1105, 2165, 260, 359,
  -100, -53, -1861, 1579, -669, -411, 532, -659, 805, 6656, -401, 487, 954,
  826, -2035]

theorem fractionalNearFrameSubtreeG5R0126_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0126Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0126Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0126Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0126_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0126LowerBoundTable : List ℤ :=
  [-175, 2864, 4008, -833, -1708, 33, -211, 2104, 181, 5229, 5580, 3730,
  1719, 5455, 2290, 6879, 1709, -3567, -1743, 99, -557, -1092, 102, 1466,
  -1949]

def fractionalNearFrameSubtreeG5R0126LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0126Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0126LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
