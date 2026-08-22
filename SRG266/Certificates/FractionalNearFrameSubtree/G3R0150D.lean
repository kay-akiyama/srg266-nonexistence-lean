import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0150`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0150Mask : ℕ := 6850211535695372

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0150Witness : Array ℤ :=
  #[-140, -272, -152, -207, -74, -21, 75, -34, 78, 28, 39, 131, 142, 69,
  119, 183, 24, -44, -82, 0, 56, 32, 87, 167, -101, 120, -71, -103, -92,
  -82, 7, 50, 49, -29, 179, 125, -82, -88, -56, -266, 51, 93, -44, -23, -36,
  84, 45, -131, 87, -82, 81, 101, 90, 67, 34, 35, -32, 19, -48, 22, -160,
  11, 38, 111, 80, 63, 75, 30, -119, 71, 209, -33, 136, 18, -111, -49, 19,
  -60, 121, -97, -219, -63, 79, 116, 16, 61, 56, 126, -183, 64, 71, -145,
  46, -147, 40, 54, -11, -80, 107, 181, -54, -115, -4, 3, -106, -69, -62,
  -40, -1, 43, -38, 14, 59, -21, 114, 5, -16, 6, 29, -101, -69, -17, -138,
  -42, -28, 57, 43, -37, 34, -27, -66, -173, 0, -107, -133, -83, -42, 214,
  -93, 292, -92, -2, 5, -33, -22, -46, 58, -147, -13, -29, -5, -40, 59, 97,
  236, -119, 73, -31, 51, -142, 38, -49, 46, 105, 112, 42, -73, -174]

theorem fractionalNearFrameSubtreeG3R0150_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0150Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0150Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0150Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0150_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0150LowerBoundTable : List ℤ :=
  [-106, 0, 111, 1, -112, 1, 26, -149, 2, -182, -8, 133, -64, 40, 10, 182,
  164, -151, 348, -420, 65, -224, 5, 236, 266]

def fractionalNearFrameSubtreeG3R0150LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0150Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0150LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
