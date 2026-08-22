import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0138`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0138Mask : ℕ := 6841900591647320

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0138Witness : Array ℤ :=
  #[6, -43, 35, 71, 15, 80, 94, 64, 16, -79, -56, -25, -28, -65, 64, 56, 58,
  201, -67, 4, 96, 42, -86, -14, 60, -159, -91, -78, 2, 64, 46, 17, -145,
  -42, 113, -5, -50, -77, -126, 15, 26, 6, 106, -76, 60, 37, -82, 9, -26,
  62, 68, 83, -112, -97, 69, 55, 39, 77, -27, -46, 96, -162, -129, -34, 11,
  115, 9, 158, 19, -1, 21, -1, -61, 82, -3, 104, -78, -75, 15, 74, -56, -79,
  -70, 41, -30, -90, 94, -48, -39, -3, 69, 57, 33, 53, -17, -76, 161, -50,
  43, 104, 31, -115, -34, -20, -52, 1, 11, -93, -93, -59, 71, 185, -22, 72,
  36, -57, 109, 84, -48, -52, -51, 179, -43, -77, -51, 99, 3, -94, -20, 99,
  16, 28, -63, 13, -8, 104, -45, 24, 18, 6, 16, 98, 91, 8, -2, 19, 27, 128,
  132, -85, 38, -83, -77, 133, 1, 117, 206, -29, -123, 116, 0, 62, 51, 40,
  101, -110, 54, -32]

theorem fractionalNearFrameSubtreeG3R0138_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0138Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0138Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0138Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0138_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0138LowerBoundTable : List ℤ :=
  [-14, 227, 102, 100, 150, 3, 14, 39, 1, 10, 234, 94, 100, 173, 9, -14,
  432, 304, 355, 10, 37, -27, 445, 241, 326]

def fractionalNearFrameSubtreeG3R0138LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0138Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0138LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
