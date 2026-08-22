import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0071`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0071Mask : ℕ := 2338374964579331

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0071Witness : Array ℤ :=
  #[121, 107, 119, 0, 18, 56, -101, -183, -164, -135, -184, -173, 86, -10,
  48, 116, 66, 105, -61, 34, 31, 44, -23, -42, 50, 61, -89, -5, 3, 0, 63,
  -94, -47, -89, -32, -50, -2, -114, 26, 96, 22, -34, -16, -47, 67, 74, 83,
  8, -14, 2, -31, 51, 64, -135, 121, -43, 29, 0, -25, -16, 30, -63, -24, 28,
  39, 53, -51, -49, -21, 49, 49, 11, 10, 74, -28, -22, -33, -11, -33, -94,
  62, 65, 21, 96, 155, 90, -117, 8, 38, 4, -82, 7, -72, 64, 44, -62, -19,
  24, 77, 24, 5, 32, -3, 15, 19, -26, 41, 54, -3, 107, -37, -5, -163, 30,
  23, -72, -41, 2, -39, -67, -37, 16, -30, -23, -51, 35, 36, -6, -16, -34,
  68, 104, 19, -16, 82, 106, -109, 8, 35, 143, 11, 63, 37, -6, 43, -14, 41,
  101, -72, 21, 92, 53, 44, -6, -140, 48, 36, 38, 116, 39, 43, -41, 119,
  -27, 0, -86, 0, 67]

theorem fractionalNearFrameSubtreeG3R0071_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0071Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0071Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0071Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0071_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0071LowerBoundTable : List ℤ :=
  [2, 195, 112, 73, 110, 3, 120, -94, 98, 59, 130, 56, -139, 9, 41, 69, 202,
  146, 217, -230, 270, -14, 302, -74, 247]

def fractionalNearFrameSubtreeG3R0071LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0071Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0071LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
