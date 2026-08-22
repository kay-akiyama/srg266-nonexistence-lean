import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0629`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0629Mask : ℕ := 11298266310758945

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0629Witness : Array ℤ :=
  #[13, 33, 29, 36, 32, 8, -37, -77, -11, -50, -52, -6, -5, 10, 35, 23, 23,
  11, 33, 1, 3, -3, -7, -4, -29, 11, -21, -26, 6, 36, -39, 10, -15, 45, 0,
  29, 3, 3, 15, 24, -80, -54, 11, -42, 74, 26, 3, -3, 4, -19, -23, 20, 8,
  -43, 49, 4, 2, -10, -12, 4, -22, 8, -29, -42, 3, -18, 36, -5, 3, 28, 2,
  27, -9, -20, 5, -52, 18, -19, -16, 24, 11, -17, -1, -22, -19, -1, -3, 2,
  -3, 24, 6, 23, -26, 36, -79, 11, 2, 12, -10, 27, -19, 34, -1, 15, 23, 1,
  -29, 13, -24, -15, -11, 15, 25, 13, -37, -4, 22, 47, -42, -23, 26, -28,
  10, -7, -14, 13, -4, 2, 40, 44, 71, 7, -21, -21, 15, -13, 34, 14, 29, 8,
  -5, 2, 11, 7, 27, 7, -1, 34, 5, -44, -28, -20, -41, -43, 49, -14, 36, -15,
  17, 31, 11, 8, -21, -22, 17, -59, 2, -37]

theorem fractionalNearFrameSubtreeG2R0629_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0629Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0629Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0629Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0629_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0629LowerBoundTable : List ℤ :=
  [-22, 2, -13, -17, 16, 2, 17, -2, 1, -40, -68, 21, 47, 10, 56, 29, 167,
  10, -40, 9, 20, 23, 12, 98, -9]

def fractionalNearFrameSubtreeG2R0629LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0629Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0629LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
