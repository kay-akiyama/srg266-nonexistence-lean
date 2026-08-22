import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0538`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0538Mask : ℕ := 6832256389419658

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0538Witness : Array ℤ :=
  #[-82, -327, 197, 133, 299, -710, 38, -650, 34, -283, 204, 405, -199, 182,
  423, -87, -250, 384, -168, -108, -521, 274, 252, 383, 197, 21, 486, 185,
  72, -626, -254, -200, 11, 1016, 809, -7, 663, -467, 1241, 182, -340, 825,
  -63, -206, 358, 48, 110, 704, -484, 55, 1041, 564, -110, 730, -4, -682,
  -167, -332, -83, 905, 518, -260, -251, 51, -254, 423, 107, 697, 549, 140,
  316, -40, 127, 118, 736, -75, 955, -80, 1089, -852, -373, -141, 247, 0,
  802, 494, 69, -659, 92, 529, -812, 238, 413, -142, -590, 231, 430, 209,
  455, -254, -476, 477, 116, 395, 256, -10, 115, 477, -303, 191, 835, 61,
  -232, -188, -463, -271, -648, 295, 902, 875, 15, 51, -386, -210, -426,
  -140, 103, 745, 0, 80, -213, -820, -198, -81, 367, -307, -118, 155, -120,
  345, -232, 82, 1175, 313, 814, 491, 11, 1380, 441, -74, -418, 406, -185,
  -215, -1017, 543, -320, 558, -251, -316, -98, -9, -357, -234, 95, 907,
  -424, -462]

theorem fractionalNearFrameSubtreeG2R0538_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0538Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0538Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0538Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0538_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0538LowerBoundTable : List ℤ :=
  [398, 224, 465, 104, 1585, 1047, 1439, 228, 1788, 3498, 928, 98, 2413,
  3087, 2102, -274, 1401, -293, -778, 1841, 1726, 4358, 3503, 99, 2384]

def fractionalNearFrameSubtreeG2R0538LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0538Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0538LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
