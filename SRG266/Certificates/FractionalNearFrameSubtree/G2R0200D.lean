import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0200`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0200Mask : ℕ := 2339541301009425

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0200Witness : Array ℤ :=
  #[0, 31, 79, 62, 112, 14, -9, -1, -47, 11, 0, 31, -41, -69, -68, -32, -56,
  -161, 155, 30, -37, -36, -183, -38, 17, -45, 13, -83, 110, 86, 82, 206,
  142, 107, 26, 49, -71, 41, -93, -163, -23, 109, -3, -195, 185, 24, -78,
  -188, 67, -28, 93, 46, 41, 28, 45, 61, 3, 61, -9, -34, -164, -71, 18, 62,
  -65, 1, 148, 15, -35, -39, 48, 58, 7, -30, 1, 76, 57, 64, 134, 26, 109,
  88, -89, -89, 4, -16, 58, 24, 55, -126, -112, -30, -147, 28, 14, -31, 15,
  2, 21, -58, 83, -35, -21, 101, 13, 85, -22, 56, 50, -4, 73, 120, 168, 27,
  43, 120, 13, -35, -227, -32, -5, 32, 66, 18, -51, -57, 22, -30, -72, 99,
  -57, -16, 37, 53, -11, 3, 14, -59, 40, 106, 14, 32, -22, 58, 33, -17, 67,
  -44, 51, -40, 12, -65, 116, 24, -30, -32, 55, -21, -120, 30, 10, 64, -84,
  -12, 54, 98, 65, -173]

theorem fractionalNearFrameSubtreeG2R0200_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0200Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0200Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0200Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0200_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0200LowerBoundTable : List ℤ :=
  [21, 59, 238, 2, 3, -129, 77, 127, 48, 10, 268, 313, 236, 186, 531, 401,
  252, -76, -173, 108, 10, -38, -27, 515, 74]

def fractionalNearFrameSubtreeG2R0200LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0200Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0200LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
