import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0125`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0125Mask : ℕ := 5402298590338584

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0125Witness : Array ℤ :=
  #[198, -277, -81, -44, 99, -122, 4, 123, -226, -72, 63, 28, 360, 451,
  -216, -183, -78, 243, 80, 12, -77, 103, 255, 195, 221, 127, 110, 120, 46,
  132, 279, 124, -119, -402, 309, -48, 179, 76, 56, 121, 61, -54, 1, 125,
  162, -154, -132, -203, 76, 329, 5, 294, 232, -20, -20, 285, -105, 78, 0,
  142, 254, 32, 0, 57, -63, -51, -124, -231, 179, 155, 85, -93, 121, 297,
  40, 410, -60, -9, -229, 111, -238, -231, 107, 97, 82, -59, 8, -74, 100,
  -222, 105, 101, -294, -24, 353, 56, 169, -97, 24, -50, -101, -162, 121,
  203, 139, 98, 157, 158, -123, 174, 329, 106, 141, -366, -193, -303, 369,
  162, -131, 143, -175, -78, 247, 15, -96, 362, -131, 141, 92, -192, 4,
  -205, -257, -90, 545, 16, 413, -98, 360, -245, 129, 114, 167, 248, 178,
  -44, 89, 77, -62, 97, 201, -271, -185, -19, -258, 16, 0, -198, -243, 172,
  143, 216, 136, 176, -59, -317, -409, -549]

theorem fractionalNearFrameSubtreeG3R0125_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0125Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0125Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0125Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0125_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0125LowerBoundTable : List ℤ :=
  [231, 146, 30, 80, 183, 130, 703, 287, 851, 635, 1046, 553, 919, -157,
  605, 740, 1208, 234, 8, -226, 385, 733, 9, 544, 531]

def fractionalNearFrameSubtreeG3R0125LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0125Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0125LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
