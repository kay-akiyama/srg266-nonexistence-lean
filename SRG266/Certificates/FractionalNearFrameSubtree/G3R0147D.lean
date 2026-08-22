import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0147`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0147Mask : ℕ := 6848705686049442

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0147Witness : Array ℤ :=
  #[32, 33, 27, 64, -60, 128, 0, -347, -63, -271, -187, 250, 181, 294, 48,
  276, 10, 64, -123, -2, -135, 263, 7, 192, 92, 159, -1, -39, -229, -16,
  -51, -122, 100, -8, -41, -80, -77, 70, 63, 177, -8, -53, -19, 42, -93,
  -82, 9, 34, -64, -37, 29, 109, 38, -32, -11, 21, -310, -71, 34, 75, 118,
  133, 86, 133, 140, 91, -259, -93, -45, 7, -41, 5, -86, -39, -124, 75, 0,
  49, -13, 103, 6, -135, 73, 28, -49, -215, 217, -53, 56, -24, 89, 52, -68,
  -18, 99, 183, -38, -53, 2, -2, -101, -211, -108, 196, 275, 284, -60, -11,
  45, 145, -288, -139, -168, -91, -90, -183, -89, 4, 203, 134, 146, 34, -64,
  -29, 23, 190, 1, 36, -30, 18, 68, 18, 87, 49, 46, -50, -17, -123, -139,
  -54, -57, -97, 77, 136, 14, 52, 66, -18, -29, -38, -99, 40, 153, 68, -77,
  20, 159, -12, -146, 14, 43, -80, -79, 29, -154, -117, -42, -180]

theorem fractionalNearFrameSubtreeG3R0147_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0147Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0147Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0147Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0147_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0147LowerBoundTable : List ℤ :=
  [-127, -112, 2, -38, 1, 140, 182, 202, -366, 292, -138, 629, -415, -582,
  371, 376, 5, -19, 140, 266, 38, 15, 86, 334, 10]

def fractionalNearFrameSubtreeG3R0147LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0147Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0147LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
