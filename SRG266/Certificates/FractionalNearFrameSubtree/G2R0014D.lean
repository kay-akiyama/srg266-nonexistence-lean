import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0014`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0014Mask : ℕ := 666978091258377

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0014Witness : Array ℤ :=
  #[-1169, -1185, -675, -1092, -973, -962, 1414, 842, 1251, 917, 1032, 298,
  -533, 377, 193, -281, 672, 0, 474, -213, -90, -28, -70, 363, 137, 253,
  -30, -304, 579, -331, 352, 161, -53, -616, -551, 364, 375, 407, 1039, 571,
  -1285, -294, -421, -304, 5, 456, 608, 819, 1649, -114, -417, -408, -659,
  569, -457, 524, 118, -205, 38, 934, 442, 42, -297, 1097, -167, 365, -361,
  301, 829, -455, 343, -2, 549, 961, 532, 71, -78, -169, -13, -328, 489,
  421, -157, 70, -211, 222, -110, -370, -31, -533, 508, 251, -547, 949, 144,
  -419, -407, -476, -29, 150, -314, -846, -219, 555, 233, -441, -799, -877,
  -891, -568, -1166, 128, -584, 700, 763, -254, 36, 892, 155, -422, -749,
  -491, 278, 192, 734, 192, 474, -588, -220, 234, 226, 643, 1122, 117, -107,
  -597, -224, 129, 203, 0, -21, 129, 707, 252, 87, 761, 0, 317, -28, -713,
  3, 598, 573, -1141, -1442, 591, -25, -276, -572, -85, -152, -185, 355,
  -546, 1197, 628, 605, -395]

theorem fractionalNearFrameSubtreeG2R0014_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0014Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0014Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0014Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0014_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0014LowerBoundTable : List ℤ :=
  [-308, 171, 527, -527, 808, 918, 225, 1186, 810, 449, 295, 1682, -895,
  1601, 1435, 1173, 100, 1036, 621, -51, 100, 101, 2103, 1263, -334]

def fractionalNearFrameSubtreeG2R0014LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0014Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0014LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
