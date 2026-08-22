import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0095`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0095Mask : ℕ := 1240006856657185

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0095Witness : Array ℤ :=
  #[0, 958, 623, -131, -520, 508, 838, 836, -1423, 296, 0, 642, -254, 471,
  -16, -1176, -1082, -675, 485, -817, -1164, -494, -1267, -282, -121, -51,
  -549, -693, 1733, 658, 1193, 1079, -54, -672, -169, -427, 109, 1811, 1209,
  749, -1090, -779, 508, -1634, -1225, 1683, 774, -428, -293, 765, 145,
  -213, 671, 0, 545, -368, 321, 1239, 994, -841, 510, -191, -589, 1393,
  1170, 797, -1395, -273, 510, -433, -86, -141, 1219, 786, 348, 130, 459,
  -7, -531, 467, 388, -73, -476, 510, 533, -317, -219, 210, -30, -412, -130,
  1001, -64, 166, 922, 1095, 967, 955, 809, -287, 345, -1298, 258, 146, 75,
  -377, -457, -157, 332, -1144, 753, -799, 877, 741, -65, -924, -571, 517,
  595, -154, 1042, -68, 48, 194, 1855, 1164, 74, -79, -145, -455, -797, 10,
  1334, -264, 449, 191, -47, 845, -199, -76, -133, -638, -118, -445, -57,
  353, -252, -162, 184, 732, 1019, 164, -626, 24, -474, -300, -299, 743,
  -191, 193, -368, 128, 25, 492, 1228, 970, 1152, 465]

theorem fractionalNearFrameSubtreeG2R0095_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0095Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0095Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0095Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0095_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0095LowerBoundTable : List ℤ :=
  [736, 1605, 2045, 359, 31, 2007, 31, 2995, 2296, 804, 3214, 3524, 1261,
  3443, 434, 99, 6590, 1786, -845, 182, 1614, -2884, -248, 2728, 5152]

def fractionalNearFrameSubtreeG2R0095LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0095Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0095LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
