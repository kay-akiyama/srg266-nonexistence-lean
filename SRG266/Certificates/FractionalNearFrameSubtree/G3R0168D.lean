import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0168`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0168Mask : ℕ := 6857213137722024

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0168Witness : Array ℤ :=
  #[131, 102, 192, 47, 93, 44, -58, -16, -238, -38, 16, 36, -102, 21, 175,
  105, 45, 28, 91, 54, 100, 97, 0, -19, -104, 74, -216, -2, -7, -3, 60, 164,
  45, -108, -12, 7, -230, 62, -161, -89, 34, -12, 29, 123, 58, 116, 75, 142,
  79, 151, -71, -205, -51, -15, -6, 18, 144, 30, 41, 2, -129, 29, 95, -87,
  -8, 32, 129, -41, 63, 128, -58, 35, 194, 0, -129, 130, -19, 31, 118, 111,
  68, -69, 62, -40, -65, 65, -85, 79, 46, 7, 9, 10, 34, 188, 23, 183, 105,
  -12, 59, 1, 279, -83, -43, 157, -28, 69, 181, -59, 212, -97, -154, -109,
  -66, -71, 38, 69, 232, 72, 80, -80, 13, 166, -90, 121, -108, 111, 115, 63,
  61, -115, 78, 143, 226, 162, -44, 19, 221, -217, -65, -85, 63, -10, -168,
  152, 155, 58, -89, -113, 210, -32, 36, -106, 31, -51, 13, 0, 168, -34,
  -63, 107, 27, -68, 286, -92, 0, 96, 206, 0]

theorem fractionalNearFrameSubtreeG3R0168_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0168Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0168Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0168Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0168_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0168LowerBoundTable : List ℤ :=
  [223, 339, 270, 412, 3, 676, 458, 133, 59, 748, 516, 207, 481, 10, 59,
  -42, -103, 124, 503, 493, 501, 422, 776, 685, 656]

def fractionalNearFrameSubtreeG3R0168LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0168Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0168LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
