import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0136`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0136Mask : ℕ := 6839908544745874

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0136Witness : Array ℤ :=
  #[162, -25, 50, 2, 29, -97, -123, -100, 84, 98, -228, 148, -76, -106, 153,
  0, 75, -85, -41, 69, -104, 120, 175, 78, -28, 55, -76, -210, -45, -35,
  121, 51, 62, 0, 94, 51, -42, 75, 18, 28, -64, -178, -118, 26, -32, -201,
  81, 74, 97, 16, 50, -62, 101, 25, 6, 8, 23, 35, -7, 27, 17, -135, 9, -2,
  24, -164, 124, -124, -75, 184, 191, -111, 86, 49, 147, 50, -73, 30, 82,
  -51, 3, -30, -9, 132, 67, 62, 45, 10, 49, -99, 24, 119, 51, 36, 37, 84,
  108, -14, 0, 11, -152, 47, 76, 82, 92, 56, 147, 104, -122, 3, 45, -28,
  -136, 70, 80, 100, -45, -28, 64, -4, 36, 198, -217, 114, -85, -34, -226,
  39, -57, 1, -117, 86, -70, -46, -146, 55, 20, -92, -28, -25, 31, 0, -32,
  -83, -79, -103, -1, -74, 35, 102, 10, 133, -68, 125, 44, 118, -35, -14,
  154, -50, 143, -24, -74, 38, -76, 0, 58, 100]

theorem fractionalNearFrameSubtreeG3R0136_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0136Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0136Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0136Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0136_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0136LowerBoundTable : List ℤ :=
  [-19, 1, 257, 212, 119, -336, 182, 184, 1, -358, 276, -109, -9, 552, 394,
  250, 10, 264, 11, 464, 296, 11, 442, -293, 606]

def fractionalNearFrameSubtreeG3R0136LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0136Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0136LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
