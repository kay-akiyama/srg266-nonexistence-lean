import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0197`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0197Mask : ℕ := 6871522692773016

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0197Witness : Array ℤ :=
  #[-38, -40, 13, 27, -55, -9, 25, -15, -15, -8, 8, -13, 22, 0, 19, 41, 37,
  -18, 70, 36, 10, 40, -4, -18, 21, -58, -57, 13, -11, -67, 39, 15, -14, 31,
  -16, 74, 23, 14, -10, -30, -74, -93, -2, -2, -20, 61, 37, 91, 1, 9, 19,
  25, 66, 29, -5, 38, 4, -25, -15, -1, -122, 23, -14, -34, 16, 29, 15, 41,
  36, 29, -6, -40, 5, 9, 4, 98, 72, -12, 27, -32, 20, -23, -14, -12, -23, 6,
  -59, 62, -51, -1, 17, 55, 34, 71, 8, 18, 1, -27, 7, -3, -31, -48, -110,
  12, -31, 52, -88, 17, -9, -3, -29, 16, -58, 6, 24, 80, 78, 105, -12, -14,
  -67, 28, -55, 54, -96, -81, -48, 26, -29, 44, 0, -25, -31, -29, -33, -56,
  47, -32, 6, 42, -47, 83, -70, 20, -85, 37, -20, -2, 39, 28, 57, -41, 21,
  87, 0, 68, -33, 7, 26, 55, 11, -30, 31, -8, 0, 73, 3, -9]

theorem fractionalNearFrameSubtreeG3R0197_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0197Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0197Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0197Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0197_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0197LowerBoundTable : List ℤ :=
  [-28, 2, -13, 2, 35, 7, 56, -49, 94, 9, 170, -20, 192, 5, -7, 70, -64,
  -108, 118, 109, 229, 26, 181, 109, 10]

def fractionalNearFrameSubtreeG3R0197LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0197Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0197LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
