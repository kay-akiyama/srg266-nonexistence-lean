import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0010`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0010Mask : ℕ := 275553696796817

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0010Witness : Array ℤ :=
  #[-124, -122, -16, -17, -128, -113, 21, 36, 62, 69, 21, 94, 25, 28, 138,
  -75, -72, 15, 94, -27, -99, 39, -25, 23, -39, 12, -57, 27, 0, 94, 33, 108,
  -28, -26, -8, 3, 3, -64, 0, 34, -79, -61, -106, -26, 48, 65, 11, 18, 85,
  194, -31, -19, -75, -18, -5, -16, -37, -48, 105, 36, 130, 41, -30, -12,
  90, -73, 34, -1, -8, 38, -6, -10, -29, -10, -8, -58, -56, 56, 12, 27, -32,
  -60, 47, -58, -10, -99, -24, -6, 13, 22, 82, 27, -14, 12, 31, -39, 26, 32,
  114, 64, 0, -44, -4, 0, 82, -32, 106, -45, -4, -25, 45, 24, -158, -23,
  -58, 10, -70, -16, 48, 14, -1, -17, 41, -84, -108, -119, 4, 5, 37, -71,
  128, 67, -14, 4, -95, -73, -10, 101, -24, 21, 36, -36, 28, 19, 8, -52, 32,
  45, 12, 43, 5, -51, 62, 9, 8, -98, -20, -48, 120, 17, -32, -89, 41, -47,
  11, 114, 70, 76]

theorem fractionalNearFrameSubtreeG3R0010_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0010Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0010Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0010Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0010_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0010LowerBoundTable : List ℤ :=
  [-98, -31, 2, 63, 1, -60, 77, -83, 66, 324, -64, 108, -353, -126, 169,
  -230, 10, 71, 178, 347, 319, -119, 104, 158, -14]

def fractionalNearFrameSubtreeG3R0010LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0010Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0010LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
