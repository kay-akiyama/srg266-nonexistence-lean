import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0206`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0206Mask : ℕ := 6881005980279960

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0206Witness : Array ℤ :=
  #[108, -96, 147, 113, -37, 97, 156, 212, 474, 216, -427, -443, -162, -222,
  -149, -54, 125, 15, -105, -82, 7, 109, 222, 63, -36, 35, 205, 158, -23,
  137, -301, 104, -195, 143, 209, -71, 81, -29, -37, 198, 131, -112, -263,
  186, 163, -368, -295, -16, 179, 167, 352, -106, 108, -100, -398, 308,
  -197, -193, 164, -229, -297, -29, 239, -250, 122, 161, 0, -269, -312,
  -271, -369, -118, 0, -104, -81, 51, 94, -163, -21, -110, 107, 351, -40,
  -273, -34, -59, -299, -42, 88, 223, 71, 28, 223, 169, -63, 25, 178, 130,
  350, 551, 205, 169, -290, 76, 25, 175, 108, 209, -232, -96, 314, 16, -66,
  19, -216, -53, 204, 139, -72, -96, 35, -40, 230, 101, -143, -160, 187, 69,
  -70, 284, 91, 83, -149, -191, -16, -183, -13, 96, 0, -163, -109, -364,
  346, 29, -31, 136, -155, 112, -121, 102, 220, 164, 140, -50, -12, 151,
  101, 85, -324, 242, 8, -59, 34, -7, -161, -69, -54, 75]

theorem fractionalNearFrameSubtreeG3R0206_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0206Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0206Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0206Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0206_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0206LowerBoundTable : List ℤ :=
  [-127, 66, 1, 275, 454, 2, -73, -113, 40, 410, -300, 224, 463, 81, 213,
  111, -795, 1303, 771, -496, 99, 190, 133, 173, 10]

def fractionalNearFrameSubtreeG3R0206LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0206Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0206LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
