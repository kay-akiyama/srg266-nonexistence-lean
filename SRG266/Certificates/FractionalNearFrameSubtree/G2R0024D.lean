import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0024`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0024Mask : ℕ := 747311025015313

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0024Witness : Array ℤ :=
  #[-64, -75, -85, -81, -80, -91, 43, 44, 41, 44, 4, 11, 66, 39, 23, 63, 14,
  51, -30, -7, -35, -10, -14, 44, 4, 27, 10, 3, -7, -7, 0, 1, -29, -20, -10,
  -10, 0, 29, 0, -11, 13, 11, -2, -7, 11, -18, -32, -27, 59, 11, 16, 19, 23,
  -18, 14, 25, 9, 25, -2, -1, -8, 69, 24, 8, 9, -10, -15, -19, -7, 31, 26,
  3, 5, 15, -12, -16, -7, -10, 20, 6, -2, 0, 1, 11, -19, -11, -23, -12, 7,
  -7, -11, 1, 13, 0, -5, 0, 8, 11, 29, 11, -16, -21, 16, 26, -16, -11, -22,
  4, 16, -60, 16, -81, 9, -97, 17, -107, 14, 64, 113, -20, -15, 16, 6, -40,
  29, 5, -31, 16, -13, 8, 0, -6, 5, -3, 20, -5, -33, -17, 26, 20, 6, -25,
  13, -15, 10, 13, -6, 6, -10, 11, 20, 5, 4, 27, -13, 32, -50, 0, 15, 25,
  23, 5, 16, -17, -9, 52, 16, -3]

theorem fractionalNearFrameSubtreeG2R0024_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0024Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0024Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0024Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0024_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0024LowerBoundTable : List ℤ :=
  [-16, 2, 1, 2, -31, 26, 89, 2, 8, 101, 94, 87, 10, -27, -10, -40, -44, 8,
  74, 26, -54, 9, 42, 117, -71]

def fractionalNearFrameSubtreeG2R0024LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0024Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0024LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
