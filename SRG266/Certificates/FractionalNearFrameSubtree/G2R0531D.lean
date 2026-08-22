import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0531`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0531Mask : ℕ := 6780397711512097

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0531Witness : Array ℤ :=
  #[149, 312, 41, 4, 212, 0, -42, 48, -82, -82, 79, -173, 36, 24, 204, -29,
  0, 71, 129, 29, -64, 81, 62, 110, -122, -10, 73, -160, -13, -56, 21, 153,
  -27, 20, -70, 50, 44, 180, 27, -29, 41, -72, -43, -28, 101, 27, 75, -77,
  -1, 59, 15, -75, -25, 43, 23, -31, -10, -43, -41, 32, 96, 47, 73, -42, -2,
  31, 11, 8, 41, 28, -121, 12, 37, -31, 0, -15, -55, 17, 19, -24, 87, 36,
  -27, -99, 17, 92, -33, 4, -68, 22, -46, -56, -74, -54, -94, -21, -30, 43,
  76, -148, 116, -22, 88, -90, -92, 21, 43, 47, 76, 66, 44, 45, -9, 16,
  -100, -26, 12, -164, -29, 24, 74, 74, 83, 0, -85, -70, 43, 20, 55, -68,
  -21, 24, -8, 26, 3, -38, -37, -94, -50, 29, -27, -7, 40, -41, 100, 118,
  24, -147, -31, 83, 40, 66, 110, 64, 57, 3, -27, -50, 98, -22, 44, -14,
  -71, 38, 36, 8, -63, -112]

theorem fractionalNearFrameSubtreeG2R0531_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0531Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0531Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0531Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0531_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0531LowerBoundTable : List ℤ :=
  [18, -19, -129, -132, 1, 292, 214, 590, 2, 165, 106, 134, 10, -232, -82,
  -19, 10, -68, 86, 247, 118, 10, 11, 499, 521]

def fractionalNearFrameSubtreeG2R0531LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0531Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0531LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
