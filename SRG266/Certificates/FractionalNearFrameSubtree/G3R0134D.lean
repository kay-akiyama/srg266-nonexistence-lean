import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0134`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0134Mask : ℕ := 6839771240010378

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0134Witness : Array ℤ :=
  #[131, 246, 42, -102, 60, 110, 88, 35, 42, -35, -68, -32, -122, -37, -107,
  -72, -77, -23, -108, -169, 5, -2, 29, 22, 178, -50, 172, 141, 68, 231,
  -82, -56, 22, 36, -32, -82, -27, 20, -81, 0, -57, -13, 28, -74, 30, 31,
  74, 6, -73, -12, 30, 37, 171, -98, -69, -191, 87, 54, 72, -7, -76, 47,
  163, 49, 187, 133, -36, 18, -130, -47, -6, 78, -19, -83, 39, 4, 179, 6,
  -112, -18, 27, 161, -36, 8, 14, -22, 129, -80, -58, 62, 4, -1, -10, 53,
  64, -47, 199, -27, 13, 28, -115, 83, -104, 100, 37, 102, 38, 15, 78, 3,
  -65, 127, 79, -121, 88, 240, 96, -53, 36, 52, -207, 177, -6, 3, 36, -156,
  -10, -177, 112, 131, -128, -19, 55, 7, -71, -150, -26, 31, 98, -91, -81,
  70, -34, 40, 50, 157, -109, 108, -12, 42, 64, -13, -35, 22, -85, 123, -11,
  69, 0, 65, 101, -68, -165, -142, -50, 161, 73, 89]

theorem fractionalNearFrameSubtreeG3R0134_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0134Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0134Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0134Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0134_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0134LowerBoundTable : List ℤ :=
  [59, 46, 250, 161, 19, 356, 1, -97, 116, 312, 113, 262, -99, 187, 186,
  -63, -79, 287, 388, 143, 9, 283, 267, 908, 236]

def fractionalNearFrameSubtreeG3R0134LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0134Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0134LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
