import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0076`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0076Mask : ℕ := 5334921446539604

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0076Witness : Array ℤ :=
  #[1134, 794, 1074, 840, 420, -130, -217, -398, 462, -316, -251, 0, 513,
  -1227, -707, -1247, 256, -305, 59, -325, -215, 101, -363, -209, -41, -347,
  264, 256, 807, 81, 107, 327, 105, 208, 408, 294, -1123, -278, 766, 241,
  233, -119, -333, -830, 348, -280, 83, 159, -97, 61, 236, 676, -25, 462,
  -670, 97, 23, 54, 173, -651, 0, -728, 415, 0, -466, -528, 474, 292, -552,
  -314, 213, -9, 404, 795, 507, 168, -58, -215, -379, -11, -438, 364, 933,
  834, 15, -489, 252, -24, -71, 438, 521, 10, 246, -1016, 32, -48, -519,
  -43, 295, -258, 453, 98, -52, -257, 111, -719, -277, -1009, -223, -155,
  350, 267, 724, 390, -155, -462, 0, -436, 258, 95, 219, -29, 0, -352, 150,
  -391, -625, 113, -178, 814, 0, 593, 323, -586, -181, 598, 623, 204, -1230,
  -231, -290, 476, 360, 708, -270, -22, -29, -839, 19, -295, -836, -156,
  405, 613, 424, -403, -605, 228, -194, -458, 93, 168, 499, -287, 482, -62,
  466, 278]

theorem fractionalNearFrameSubtreeG5R0076_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0076Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0076Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0076Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0076_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0076LowerBoundTable : List ℤ :=
  [-300, 32, 293, 31, 31, 32, 31, 572, 252, 847, -1594, -1935, 505, 1103,
  1947, 1742, 99, -274, 1154, 100, -788, 2643, -199, -344, -67]

def fractionalNearFrameSubtreeG5R0076LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0076Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0076LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
