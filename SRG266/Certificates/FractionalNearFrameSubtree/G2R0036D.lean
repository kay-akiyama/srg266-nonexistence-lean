import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0036`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0036Mask : ℕ := 883718949421571

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0036Witness : Array ℤ :=
  #[15, 36, 30, 16, 66, 4, -3, -26, -3, -19, 0, -29, 0, 19, 1, 5, 7, -50,
  40, 92, 49, 6, 29, 8, -75, 64, 5, 57, -13, -7, -23, -36, -48, 40, 40, 16,
  -28, -20, -51, -22, -29, -25, 38, 79, 76, -10, 83, -2, 2, 27, 4, -31, 7,
  13, 10, 6, -25, 30, -45, 59, -16, 21, -14, 22, -67, -79, 61, -39, 16, -5,
  31, 15, -18, 13, -12, 13, -37, -13, 48, 29, 16, -8, 25, -12, 73, 15, -8,
  70, 44, -21, -10, -9, 13, 26, 11, -14, -5, 14, 56, 5, 1, -4, 32, 50, 8,
  -16, 27, 1, 18, 28, 29, -16, 25, -25, 17, 65, -1, -3, -30, -57, 37, -22,
  -25, -8, 6, 34, -19, 17, 22, 41, 18, 2, -30, -10, 2, 9, 25, -15, 20, 11,
  19, 20, -46, -2, 2, -21, 3, 34, -19, 19, 40, 37, -21, 0, 2, 39, -21, 6,
  45, -19, -81, -2, 11, 48, -14, 65, 78, -104]

theorem fractionalNearFrameSubtreeG2R0036_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0036Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0036Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0036Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0036_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0036LowerBoundTable : List ℤ :=
  [48, 100, 46, 73, -61, 141, 27, 55, 146, 175, 224, 12, 109, 12, 176, 49,
  313, 23, 193, 103, 314, 38, 10, 9, 10]

def fractionalNearFrameSubtreeG2R0036LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0036Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0036LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
