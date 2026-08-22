import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0071`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0071Mask : ℕ := 5264721069203729

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0071Witness : Array ℤ :=
  #[15, -51, 11, 50, 7, 8, 4, 1, 16, -11, 42, 15, -24, -99, -46, -85, -35,
  -65, -68, -6, -34, -3, -21, -15, -76, -65, 60, 80, 52, 26, 30, -86, 10,
  17, 23, 25, 54, 25, 39, -58, -64, 13, 46, 34, 50, 26, -17, -35, 59, 47,
  -47, -42, 104, -92, -99, 0, -70, -28, 11, 39, 60, -84, 31, 55, 64, 67, 14,
  43, 66, -53, 74, -2, 80, 67, -22, 11, -28, 7, 13, -34, -83, 90, 45, 5,
  -22, -20, -32, -35, 28, 8, -4, -20, 59, -24, 18, -66, -7, -41, 36, -17,
  66, 66, 81, 5, -4, 75, -52, -30, -35, 9, -11, 7, 0, -29, -69, 57, -30, 57,
  74, 20, -22, -52, -86, 68, 8, 34, -38, -49, 40, -55, 43, -6, -60, 25, 28,
  44, 62, 23, 37, 69, 74, -43, -10, 42, 36, 129, 32, 65, 77, 22, -41, -28,
  -87, -16, -21, -79, 66, -74, -92, 12, 21, 15, 41, 56, 57, 8, 3, 52]

theorem fractionalNearFrameSubtreeG5R0071_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0071Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0071Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0071Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0071_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0071LowerBoundTable : List ℤ :=
  [-5, 114, 79, -38, 97, 88, 16, 2, 38, 99, 152, 155, -52, 198, 179, 99,
  265, -134, 63, 9, 11, 49, -108, 9, 240]

def fractionalNearFrameSubtreeG5R0071LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0071Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0071LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
