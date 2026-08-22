import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0092`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0092Mask : ℕ := 2511544022697042

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0092Witness : Array ℤ :=
  #[-26, -57, -133, -31, 82, -35, 106, 86, 216, 89, 100, -19, 50, 0, -56,
  -35, 58, 60, 35, 26, 164, -35, 13, 65, -14, -52, 31, -66, -33, -21, -10,
  32, 52, 25, 18, 0, 120, 20, 61, -109, -113, -27, 19, -17, 24, -64, 3,
  -175, -3, 128, 41, 31, 78, -27, 38, -70, 108, 7, 93, 46, -6, -10, 75, 57,
  20, 56, 104, -79, 86, -5, 67, 86, 30, -44, -13, -72, 131, 70, -109, 76,
  85, -3, 21, 11, -27, -64, -66, -140, 101, 76, 13, 100, -44, -21, 69, 83,
  -133, 127, -55, -67, -25, -63, 11, 33, -31, 54, -47, -77, 127, -49, 39,
  57, -73, 42, -4, -6, 3, 145, -55, 12, 30, 41, 8, -9, 30, -21, -6, 157,
  -32, 52, 75, 60, 31, -14, 124, -67, -45, 13, -8, -14, 31, -76, 86, -27,
  70, -48, 28, 81, 78, 17, 8, 42, -37, 105, 126, -17, 44, 13, 7, -77, 45,
  97, 78, 61, 88, 0, -1, 75]

theorem fractionalNearFrameSubtreeG3R0092_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0092Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0092Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0092Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0092_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0092LowerBoundTable : List ℤ :=
  [140, 257, 54, 154, 90, 211, 231, 197, 179, 268, 331, 187, 108, 176, 229,
  -17, 90, 572, 266, 10, 509, 289, 332, 613, 345]

def fractionalNearFrameSubtreeG3R0092LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0092Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0092LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
