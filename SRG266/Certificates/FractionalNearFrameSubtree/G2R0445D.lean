import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0445`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0445Mask : ℕ := 5790962011247762

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0445Witness : Array ℤ :=
  #[-12, 77, 18, 0, -27, 63, 97, -6, 7, 25, -30, -2, 0, 11, -25, -60, -24,
  29, 4, -1, -4, 50, 3, -32, -4, 19, 3, 12, 10, -34, -30, -75, 6, 31, -23,
  29, 48, -32, 33, 30, -13, 23, -1, -7, -38, 82, -19, 12, -8, -8, -33, -26,
  -22, -39, -39, 74, -26, 4, -9, 27, 25, 11, 15, 18, 36, 77, -72, -39, 7,
  21, 8, -16, 13, -26, -31, 17, 21, 34, -1, -18, 21, -41, 8, -10, -55, -40,
  39, 22, 4, 47, 19, 9, 6, 27, 34, -23, 24, 9, -75, -47, -65, -40, -62, 42,
  -113, 12, 0, -38, -21, 2, 17, -5, -79, 44, -10, -17, -42, 12, -20, 33, 25,
  20, 15, -14, -17, 19, 57, 23, -13, 35, 31, -33, 12, 24, -34, 21, -41, 20,
  23, -30, 42, -7, 21, -31, -12, -65, -26, 16, -91, 5, -27, 7, -43, 30, 39,
  -66, 14, 8, 61, 25, 42, 42, 1, 11, 4, 49, 32, 30]

theorem fractionalNearFrameSubtreeG2R0445_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0445Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0445Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0445Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0445_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0445LowerBoundTable : List ℤ :=
  [-49, 3, 1, 93, -91, 54, 2, 2, 22, 110, 12, -56, 154, -125, -189, -27, 96,
  103, 93, -83, 11, 28, 9, 34, 238]

def fractionalNearFrameSubtreeG2R0445LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0445Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0445LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
