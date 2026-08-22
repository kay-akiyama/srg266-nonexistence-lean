import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0041`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0041Mask : ℕ := 2517020791783939

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0041Witness : Array ℤ :=
  #[186, -78, -67, 70, 20, 137, -38, -55, -142, 0, 23, -15, 78, -141, -45,
  -39, 299, -47, 21, -17, -3, 41, -256, -188, -339, -240, -251, 200, 204,
  102, 88, 92, 118, 4, 7, 90, -38, 58, 16, -115, 8, -85, -33, -181, -154,
  20, 121, -202, -144, -241, -90, 326, 12, 326, 257, -218, -154, 200, 229,
  -227, -311, 14, -28, 10, 6, -42, -32, 176, 92, -87, -43, -62, 52, -56,
  -34, 147, 39, 190, 36, -34, -19, -3, -20, 20, 14, 15, -40, -3, 106, 62,
  -63, 33, 7, 65, 95, 129, -23, -29, 153, -24, 80, 37, 28, 97, -6, -77, -22,
  104, -91, 33, 13, 8, 27, 86, 29, 11, -89, -39, 5, 6, 83, 157, 155, -144,
  -52, -27, 107, 87, -147, 126, 70, 8, -23, -116, 30, 0, -69, -21, -24, 137,
  -2, -69, -12, 114, 41, -44, 24, 34, -9, 3, 35, 60, -7, -32, -96, -36, 31,
  78, -61, 44, -57, -178, 136, 100, 50, 21, 16, 4]

theorem fractionalNearFrameSubtreeG5R0041_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0041Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0041Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0041Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0041_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0041LowerBoundTable : List ℤ :=
  [-82, 81, 1, -168, 3, 283, 38, 2, 2, 10, 10, 10, 176, 105, 623, -247,
  -155, -29, 10, 10, 252, 11, 616, 538, 150]

def fractionalNearFrameSubtreeG5R0041LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0041Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0041LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
