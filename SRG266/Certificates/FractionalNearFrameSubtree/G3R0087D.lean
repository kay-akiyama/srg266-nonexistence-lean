import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0087`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0087Mask : ℕ := 2487843787543202

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0087Witness : Array ℤ :=
  #[92, 78, 7, -9, 27, 75, 43, -81, -123, -38, -28, -40, 48, -70, 68, -6,
  -5, -4, -28, -42, -49, 21, 51, 49, -32, -52, 36, -30, 61, 75, -6, 5, -47,
  46, 34, -32, 12, 16, 36, -35, 2, -98, -11, 2, -61, 50, 52, 8, -19, -9,
  -45, -82, 32, -30, -25, 11, -7, -13, -54, -4, 9, 4, 44, 49, -8, 46, -74,
  43, -50, 30, 31, 36, -5, -34, -80, -26, 37, 7, 78, 35, -32, 53, 38, -78,
  109, 1, -56, 19, -52, 6, 81, 8, 61, 59, -23, -30, 59, -34, -28, -35, -66,
  28, 5, 3, -63, -10, 9, -14, 47, -30, -26, 73, -10, 73, 55, 35, -17, 32,
  19, -83, -2, -88, -20, 48, 15, -15, 22, 45, 12, 58, 76, -24, 93, 81, -35,
  -23, 76, 71, 4, 13, 58, -23, 1, 3, 8, 32, 72, 23, -2, -34, 3, 23, -5, 34,
  14, -31, -96, -20, -8, -53, 36, -64, 21, -58, 0, 33, 72, -16]

theorem fractionalNearFrameSubtreeG3R0087_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0087Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0087Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0087Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0087_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0087LowerBoundTable : List ℤ :=
  [-46, 73, -41, 1, 19, 5, 86, 22, 87, 7, 62, 135, 257, 71, -72, 114, 78,
  339, -28, 91, 11, -43, 124, 226, 61]

def fractionalNearFrameSubtreeG3R0087LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0087Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0087LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
