import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0207`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0207Mask : ℕ := 6881006169017880

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0207Witness : Array ℤ :=
  #[121, -39, -11, -32, -169, 137, 14, 149, 80, 91, -87, -88, -37, -105, 3,
  -105, -130, -59, -198, 58, 79, 32, -15, 49, 50, 179, 67, 40, 38, -117, 29,
  -71, 22, 80, -54, -63, 74, -35, 82, -115, -57, 37, -42, -107, -19, 11, 86,
  38, 69, 12, -49, 45, 35, -89, 132, -30, 16, 41, -70, 148, -120, 0, -19,
  -41, -97, 105, 80, 32, 126, 88, 83, 71, 38, 38, -26, 84, -22, 52, -100,
  37, 0, 32, -39, 9, -139, 91, -35, 3, 184, 130, -1, 91, 83, 44, 182, 60,
  45, 145, 35, -86, -9, 39, 12, 36, 80, 135, -71, 58, -18, -92, -142, 43,
  -66, -63, 78, -65, 112, 91, 0, 25, -170, 45, 12, 102, -68, -69, 51, -75,
  44, -19, -116, 132, -88, -30, -27, 2, 126, -21, 0, 89, -26, 44, 28, -102,
  69, 114, 76, -13, -45, -40, 3, 103, -33, -65, 11, 87, -86, -48, -124, 146,
  -111, 12, 83, -70, -46, 24, 62, 80]

theorem fractionalNearFrameSubtreeG3R0207_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0207Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0207Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0207Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0207_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0207LowerBoundTable : List ℤ :=
  [-5, -1, -14, 192, 160, 1, 224, 87, 59, 9, 160, 415, 85, 239, 147, 301,
  -141, 9, 453, 200, -75, 412, 350, 30, 404]

def fractionalNearFrameSubtreeG3R0207LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0207Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0207LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
