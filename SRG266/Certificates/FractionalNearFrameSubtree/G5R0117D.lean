import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0117`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0117Mask : ℕ := 5794198866995489

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0117Witness : Array ℤ :=
  #[68, -60, -34, 112, -36, -36, 0, 34, 80, -199, -25, -7, -5, 201, 0, 18,
  115, 113, 106, -5, -19, 50, -73, -8, 224, -58, -26, 0, -16, 122, 124, -90,
  83, 85, -90, -130, -121, -235, -174, 99, 107, -48, -2, 85, 125, 6, -89,
  111, -121, -202, 2, -63, -141, 287, -9, 93, 85, -97, 251, 49, 159, -81,
  28, 137, -188, -138, 195, 45, 69, 77, 66, -106, 79, -37, 25, 143, 11,
  -110, 261, -134, 176, 35, -96, 153, -158, 17, 0, -11, -101, 0, 16, 9,
  -150, 151, 164, 16, -4, 103, 40, 121, 80, 67, -154, 82, 4, -91, -118, 142,
  45, 59, -64, 97, 109, 151, 35, -75, 72, -21, 64, 8, 80, -101, -13, -154,
  -55, 39, 117, 133, -91, -87, -250, -13, -134, -19, -36, -67, 102, 65, 24,
  0, 86, 65, -208, -32, 113, 9, 54, 225, 153, 102, -10, 220, -226, 16, 22,
  -70, -13, 16, 57, 18, 21, -288, 34, 104, 76, -44, -111, -100]

theorem fractionalNearFrameSubtreeG5R0117_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0117Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0117Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0117Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0117_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0117LowerBoundTable : List ℤ :=
  [-14, 63, 108, 369, 3, 125, 130, 3, 2, 183, 448, -191, -98, 402, 388, 9,
  -157, 11, 263, 1103, -156, 374, 207, 306, 521]

def fractionalNearFrameSubtreeG5R0117LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0117Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0117LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
