import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0030`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0030Mask : ℕ := 506792494547590

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0030Witness : Array ℤ :=
  #[9, -55, 46, -55, 6, 34, -117, 0, 9, -23, 6, -44, 16, 34, 23, 28, 2, 53,
  31, -36, -51, 0, 6, 48, 91, -19, 78, 26, 34, -15, -41, -18, -72, -58, 0,
  -8, 44, 18, -31, -9, -6, -22, 76, 30, -7, -6, -27, -76, -105, -85, 56,
  -30, 0, -5, 74, 3, 68, 38, 36, -50, -80, 0, -23, 75, 47, 27, 87, 61, -25,
  -24, -5, 79, 48, -5, 8, -20, -33, 20, 19, 122, -43, 16, -8, -3, 35, 82,
  48, 35, 9, 44, -73, 4, -14, 31, -21, -18, -29, 21, 24, -63, 23, 1, -55,
  30, -43, -51, 25, 2, -23, -90, -2, -31, -23, 28, 40, 20, 67, 79, 102, -59,
  -41, -23, 35, 47, 16, 19, 13, 7, 22, 65, 5, 21, -21, -27, 21, 35, 1, 9, 5,
  8, 16, 5, 6, -49, -14, -28, 4, 25, 15, -69, -38, 36, 9, -26, 0, 4, -65,
  -8, -1, -65, 109, -63, -66, -10, 27, 22, 0, 11]

theorem fractionalNearFrameSubtreeG1R0030_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0030Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0030Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0030Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0030_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0030LowerBoundTable : List ℤ :=
  [-27, 22, -52, 41, 3, -20, 48, 77, 2, 60, 143, 134, 30, 114, 9, 39, 79,
  39, -20, 212, 66, 27, 225, 124, 11]

def fractionalNearFrameSubtreeG1R0030LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0030Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0030LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
