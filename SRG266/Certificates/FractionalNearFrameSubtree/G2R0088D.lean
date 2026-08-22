import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0088`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0088Mask : ℕ := 1213631829876809

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0088Witness : Array ℤ :=
  #[90, 31, -6, 4, 59, 63, -58, 50, -38, 1, 68, -135, -118, -35, 42, -37,
  -91, -64, 38, 48, -49, -74, -33, -9, -129, -86, -101, -221, 154, 144, 126,
  123, -67, -95, -75, -32, 67, 118, -32, 20, 0, 55, 19, -45, 13, -84, -106,
  47, 82, 105, -39, -33, -55, -131, -99, -83, 22, 9, 0, -61, -71, -29, 48,
  -38, 78, 61, 73, 33, -10, -34, -22, 104, -61, -48, 73, -44, 115, 36, 96,
  18, 19, 14, 25, 114, 80, -82, 34, -21, 32, 22, -7, -49, 62, 84, 42, 15,
  -80, 19, -5, 43, 41, -122, -144, 96, 24, -21, 18, 64, 35, -68, -2, -31,
  -13, -81, 56, 32, -40, 54, -39, -125, 54, 37, -8, -15, 188, -61, 22, -34,
  -49, -13, 42, -52, -4, 34, 69, 98, -11, 9, 1, 74, -10, 34, -13, 36, 5, 53,
  63, 65, 65, 33, 50, 81, 131, -42, 25, -49, -43, 2, -19, -77, -16, 33, -26,
  -65, 49, 5, 72, 68]

theorem fractionalNearFrameSubtreeG2R0088_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0088Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0088Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0088Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0088_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0088LowerBoundTable : List ℤ :=
  [-65, 136, 69, -52, 2, 84, 40, 56, 1, 98, 442, 232, -33, 2, 397, -205,
  -15, 424, -145, -216, -50, 9, 104, 110, 176]

def fractionalNearFrameSubtreeG2R0088LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0088Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0088LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
