import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0300`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0300Mask : ℕ := 5387215903005336

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0300Witness : Array ℤ :=
  #[-44, 16, -29, -26, -20, 0, 22, 15, 26, -3, -11, -10, 21, -15, -30, -31,
  4, -8, -14, 9, 37, 33, -5, 28, -1, 3, 12, -25, -44, -50, -65, 6, 17, -24,
  -9, 37, 34, 66, -19, 31, 5, 25, 0, 5, 30, 27, -34, -29, 37, 51, 15, -29,
  -54, -30, -38, 36, 6, 9, 0, -7, 5, 2, 9, 14, -36, 14, -21, -11, 57, 42,
  45, -6, -49, 25, -6, 41, -42, -18, 15, -31, -19, 41, 18, -23, -17, 19, 19,
  -24, 32, -3, 4, 36, 9, 7, 33, 44, 14, -16, 12, 42, 16, 42, 54, 24, 38, 20,
  6, -7, 4, -40, -9, 3, -21, 8, 0, 19, 13, 27, 8, -5, -5, -34, 14, 47, 30,
  -42, -16, -10, 2, 10, 16, 24, -42, -59, -21, -23, 4, -35, 22, 22, -11, -1,
  -43, 10, -39, -30, -43, 23, 19, 23, 26, 22, 73, -1, 13, 33, 46, -46, 40,
  -29, 21, -39, 3, -22, 29, 32, 69, 0]

theorem fractionalNearFrameSubtreeG2R0300_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0300Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0300Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0300Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0300_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0300LowerBoundTable : List ℤ :=
  [11, 31, 118, 99, 3, 78, 3, -71, 3, 203, -146, -133, 35, 83, 157, 63, 21,
  84, 168, 19, -37, 84, 19, 219, 116]

def fractionalNearFrameSubtreeG2R0300LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0300Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0300LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
