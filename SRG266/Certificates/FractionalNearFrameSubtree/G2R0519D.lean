import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0519`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0519Mask : ℕ := 5827654180127336

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0519Witness : Array ℤ :=
  #[23, 0, 20, 46, -7, 32, -17, 90, -27, -9, 14, -49, -47, -40, 83, 32, 0,
  98, 69, 69, 77, -81, 76, -17, -33, -62, 19, -138, -15, -19, -54, 6, -3,
  49, 9, 0, 79, -49, -70, -18, 17, 18, 60, 29, -8, 12, -21, 12, -42, -26,
  -23, -33, 0, -10, 37, -6, 6, -27, -30, 73, -60, -109, -46, 20, 14, 33, 46,
  70, 25, -22, 15, -48, 23, -92, -39, 25, 72, -43, -30, -38, 56, 53, -11,
  17, -56, 71, 8, 58, 26, 5, -21, -38, 67, 4, -23, 2, 46, -78, 28, 11, -13,
  4, -58, 77, 26, 47, 70, -13, -72, -43, -59, -13, -8, 31, -65, 9, 55, -24,
  -27, -21, -29, 18, 23, -10, 43, -40, 18, -93, -77, 17, 50, -29, -50, 24,
  5, -25, 12, 0, 48, -37, 76, 74, 40, 19, -80, -3, 9, 82, -25, -10, -96, -6,
  -52, 56, 76, 43, 6, -6, 24, -15, 26, 69, 38, 22, 22, -9, 124, -37]

theorem fractionalNearFrameSubtreeG2R0519_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0519Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0519Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0519Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0519_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0519LowerBoundTable : List ℤ :=
  [-39, 41, 16, -3, 27, 15, 81, 1, 48, 36, 11, 103, 10, 57, 9, -168, 13, 22,
  9, 45, 344, 233, 10, 267, 8]

def fractionalNearFrameSubtreeG2R0519LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0519Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0519LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
