import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0146`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0146Mask : ℕ := 1039678196585060

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0146Witness : Array ℤ :=
  #[-164, -37, -13, 7, -19, 125, 75, 133, 80, 94, -18, -13, 10, -24, -44,
  11, -9, -101, -69, -6, 6, -18, -139, -249, 256, 236, 212, 147, 148, -124,
  2, 41, -124, 57, 87, 161, -124, -170, 43, 198, 152, 219, 58, -9, -26, 68,
  -28, -13, 103, 68, 112, 35, -68, 32, -153, 34, 0, 34, -1, -35, -165, -17,
  -55, 70, -60, 205, 82, 63, -47, 122, -115, 47, -76, 48, -4, 91, 31, -130,
  -9, 72, -40, 68, 83, 21, 80, 52, 166, 21, -103, -11, 104, 45, 13, 67, 13,
  -159, 22, -26, 16, -46, 45, -41, 54, 76, -83, -85, 67, 59, 59, -117, 61,
  9, 22, -31, 175, 76, 185, 119, 110, 15, -17, -239, -53, 51, 180, -95, -84,
  27, -67, -2, -108, 40, 48, 6, -22, -63, -52, -21, 79, -65, 62, 19, 54, 39,
  124, -14, 221, 24, -8, 18, -72, -111, -71, 28, -49, -80, -42, -125, 25,
  -45, 9, -79, 63, -167, -142, -3, -17, -64]

theorem fractionalNearFrameSubtreeG1R0146_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0146Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0146Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0146Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0146_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0146LowerBoundTable : List ℤ :=
  [-4, 2, 48, -48, 129, 229, 202, 2, 250, -58, 421, -95, -27, 10, 247, -154,
  507, 239, 10, -138, 586, 131, 443, 303, 455]

def fractionalNearFrameSubtreeG1R0146LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0146Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0146LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
