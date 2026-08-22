import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0124`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0124Mask : ℕ := 5402298149950104

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0124Witness : Array ℤ :=
  #[29, 16, 54, 8, -13, -13, 17, 11, 56, 37, -55, -14, 27, -57, -5, 23, 82,
  -22, -31, -9, 27, 5, 3, 37, 24, 67, 40, 0, -30, -2, -14, -6, -23, 1, 37,
  -29, 36, -61, -34, 34, -22, 0, 14, 9, -19, -17, -61, -44, 0, -39, 59, 18,
  100, 41, 36, -51, 59, 98, -65, -29, 0, -9, 45, -14, 84, -47, -163, 98, 33,
  -45, -66, -31, 11, -192, -119, 54, -32, 10, 15, -5, 20, -11, -9, -23, 42,
  -93, 1, 46, -56, -10, 5, 56, -104, -77, 29, -107, -57, -44, 46, -75, 33,
  82, 110, 80, 5, -9, -16, 42, -47, 38, -19, 6, 29, 166, 1, -13, 79, -85,
  -15, -69, -7, 65, -4, -106, 18, 37, -14, 17, -34, 0, 27, -90, 21, 40, -86,
  138, 0, 2, -139, 28, 25, -60, 22, -20, -40, 35, -6, 17, 66, 30, -36, -53,
  7, -72, 39, 38, 55, 13, 22, -58, -116, 44, 28, -73, 69, 119, 0, -26]

theorem fractionalNearFrameSubtreeG3R0124_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0124Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0124Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0124Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0124_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0124LowerBoundTable : List ℤ :=
  [-70, 2, 3, 89, 102, -20, -137, -109, -28, 136, -52, -7, 10, 136, 131,
  -280, -25, 13, 262, 132, 9, 190, 10, -149, -6]

def fractionalNearFrameSubtreeG3R0124LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0124Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0124LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
