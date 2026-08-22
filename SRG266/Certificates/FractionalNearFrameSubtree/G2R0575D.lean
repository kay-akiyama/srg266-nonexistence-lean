import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0575`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0575Mask : ℕ := 6848680381616930

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0575Witness : Array ℤ :=
  #[499, -178, -1, -234, -375, -350, 913, 567, 600, 505, 248, -171, -461,
  -167, 132, -772, 287, -40, 167, 196, -370, 52, -245, 225, -199, -53, -19,
  209, -178, -111, 437, 251, 695, -426, -173, -236, -75, -145, -88, 9, 70,
  -71, -554, 1, 514, 453, -124, -158, 14, -29, 154, -143, -87, 418, -16,
  173, 323, 134, 457, 105, -724, -532, 508, 431, 483, -552, 36, -358, 339,
  -149, -180, -82, -125, -113, 30, -50, -17, -29, 178, -215, 339, 303, 167,
  98, 181, -179, 209, -12, 427, 40, 320, -295, -71, 186, 22, 13, -311, -152,
  -121, 342, -92, -25, -67, -188, -51, 287, 172, 46, -317, 0, -52, 291,
  -237, -304, -97, -161, -443, -107, -181, 56, 284, 345, 19, -249, -97, -67,
  187, 51, -239, 327, 69, 110, 115, -116, 29, -453, 566, -553, 141, 96, 368,
  5, 207, 2, 120, -76, 271, 21, -8, -41, 550, 223, 257, -46, -11, 140, 356,
  243, 224, 369, -24, 76, -167, -168, -319, 194, 429, 160]

theorem fractionalNearFrameSubtreeG2R0575_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0575Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0575Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0575Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0575_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0575LowerBoundTable : List ℤ :=
  [-7, 540, 1073, 188, -45, 78, 61, 273, 879, 421, 1041, 185, 395, 950, 885,
  907, 2118, -50, -92, 945, 409, -60, -531, -960, 719]

def fractionalNearFrameSubtreeG2R0575LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0575Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0575LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
