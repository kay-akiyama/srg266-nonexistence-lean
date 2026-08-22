import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0241`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0241Mask : ℕ := 5109140305994001

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0241Witness : Array ℤ :=
  #[89, 72, 38, 59, 15, 27, -81, -54, -111, -125, -135, -89, 58, 107, 73,
  29, 10, 0, 76, -2, 24, 24, -4, -8, -5, -48, -22, -51, 14, -12, 27, 7, 154,
  33, 83, -74, -6, 28, -17, -9, -91, -70, -13, -174, -29, 147, 80, -4, -20,
  -4, 8, -28, -11, -10, -40, 27, -4, 27, 28, 11, 32, 11, 13, -8, -1, -16,
  -21, 11, 9, -20, 14, 1, 20, 6, -1, 19, 43, 6, -2, 24, 7, 2, -1, 5, -39,
  10, 11, 16, -8, -12, 4, -8, -3, 39, 0, -5, 15, 20, 19, 13, 5, 21, -12, 51,
  15, -4, 5, 47, -7, -37, -25, -53, -37, -48, 22, 52, 37, 45, 15, -21, 16,
  22, -57, -40, 12, 3, -35, 1, 7, -3, -14, 0, -14, 11, -36, -6, 34, -2, 20,
  -11, 21, -15, 10, 38, 17, 9, 10, 2, 50, 6, -3, -7, 25, -12, 42, -16, -19,
  -23, 10, -3, 10, -17, 6, -25, -26, 17, 12, 5]

theorem fractionalNearFrameSubtreeG2R0241_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0241Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0241Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0241Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0241_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0241LowerBoundTable : List ℤ :=
  [-16, 2, 87, 15, -104, 104, -6, 2, 138, 13, 56, -14, -82, 10, 65, 115,
  251, 106, 10, -2, 34, 75, 10, 53, -88]

def fractionalNearFrameSubtreeG2R0241LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0241Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0241LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
