import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0095`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0095Mask : ℕ := 5512178462998868

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0095Witness : Array ℤ :=
  #[-241, -641, -1221, -703, 211, 245, 0, -134, -552, 401, -180, 214, 614,
  651, 268, 973, -200, -87, -410, 374, 400, 146, 597, -1, -96, 287, -308,
  -259, 405, -724, 201, -234, -226, 599, -196, -394, 795, 950, 5, -634,
  -206, 459, 672, 0, -302, -323, 404, 620, 590, 971, -348, 175, 306, 508,
  -701, -287, -258, -836, -150, 529, 36, 692, 0, 467, 314, 355, 681, -242,
  -165, 379, 203, 35, 109, -72, -736, 443, 90, 127, -67, 720, 27, 225, 32,
  47, 183, 65, 510, -175, 435, 310, -260, -410, -767, 294, 238, 470, 189,
  -281, -477, -366, -51, -383, -724, 185, -360, 314, -31, 463, -24, 168,
  -200, 63, -782, -352, -1281, 194, 165, -16, -211, 278, 405, 137, -668,
  -202, 296, -247, -665, -426, -720, 867, 199, -44, 65, 322, -1110, 866,
  -27, -105, 523, 709, 540, -411, -113, -1377, 76, 607, 112, 227, 457, -220,
  -456, 509, -396, 218, -228, 74, 635, -562, 411, 1011, 385, 313, 369, 418,
  392, 50, 337, 371]

theorem fractionalNearFrameSubtreeG5R0095_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0095Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0095Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0095Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0095_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0095LowerBoundTable : List ℤ :=
  [6, 560, 372, -173, 715, 1051, 1, -329, 869, 1289, -66, 422, 1007, -20,
  127, 1878, 559, 1408, -1603, 1649, 1459, 1818, 726, 2070, 1418]

def fractionalNearFrameSubtreeG5R0095LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0095Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0095LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
