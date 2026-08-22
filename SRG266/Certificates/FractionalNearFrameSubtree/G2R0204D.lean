import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0204`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0204Mask : ℕ := 2348328804096545

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0204Witness : Array ℤ :=
  #[0, -5, 3, 15, -29, 13, 2, 44, -3, -16, 23, 42, -54, -34, -63, -17, -8,
  0, 68, 59, 42, 21, -26, -50, -2, -22, -53, -31, 12, 18, -23, 86, 1, 12, 0,
  20, -11, -11, -39, -16, -8, 8, -7, 38, 48, -36, -9, -32, 65, 10, 30, 2,
  35, 2, 23, -10, -35, 2, -13, -22, -32, -4, 3, 1, 26, -8, 22, 23, -14, 5,
  -38, -22, 36, 52, -40, -21, -17, 75, -25, 16, -10, 21, 37, 26, -7, 5, -20,
  -7, 54, -43, -63, -1, 32, 61, -32, 23, 33, 0, 81, -56, -5, -46, -5, 26,
  50, -19, 21, -18, 45, 18, -7, 15, -6, 22, 43, 31, 13, 41, -120, 14, -26,
  28, 37, 21, -29, -57, 29, -23, 2, -41, 37, -36, 7, -15, 34, 47, 7, -6, 37,
  3, 27, -4, -22, 7, -17, 12, 1, -35, -49, 5, -30, 16, -15, 12, -55, -26,
  46, 46, -46, -7, 6, 14, 21, 5, 29, 18, 0, -55]

theorem fractionalNearFrameSubtreeG2R0204_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0204Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0204Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0204Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0204_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0204LowerBoundTable : List ℤ :=
  [-32, -51, 121, 10, 7, 2, 2, 38, 16, -85, 10, 217, 173, 67, 72, 85, 108,
  -44, 73, 24, 47, 60, -173, 151, 11]

def fractionalNearFrameSubtreeG2R0204LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0204Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0204LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
