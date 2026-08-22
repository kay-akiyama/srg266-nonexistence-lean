import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0534`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0534Mask : ℕ := 6794669082784785

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0534Witness : Array ℤ :=
  #[83, 56, 20, 6, 140, 64, -7, -54, 9, 8, -29, -80, 109, 27, 170, 84, 20,
  0, 87, 80, -22, -6, 12, 44, 68, 61, 25, 9, -16, 36, -37, 0, -6, 140, -67,
  76, 25, 26, -22, -13, -64, -79, -94, 50, 146, 52, 21, 12, -3, 15, -5, -7,
  -71, 9, 55, -2, -16, -7, 0, -33, 11, 19, 35, -12, 7, 83, 8, -25, 48, -29,
  43, 23, 28, 21, -30, 39, -22, 13, 1, -29, -9, -18, 3, 41, -71, 66, -26,
  38, 17, -12, 72, 33, -39, -11, -13, -72, -31, 8, 5, 0, -34, -26, 25, 42,
  -11, -42, 2, 32, 31, 14, 55, 44, 28, 18, 42, 48, -47, -32, 44, 3, 39, -18,
  -71, -14, 44, -9, 13, -22, -49, -18, 83, 17, -11, 26, 53, 0, 23, 35, 39,
  -34, -23, -17, -63, -20, -34, 33, -16, 15, -43, 7, 36, 33, -34, -18, -13,
  -31, 10, -11, 5, -68, 117, -28, 40, 14, -9, -23, 45, -105]

theorem fractionalNearFrameSubtreeG2R0534_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0534Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0534Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0534Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0534_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0534LowerBoundTable : List ℤ :=
  [74, -25, 2, -6, 3, 170, 297, 374, 152, 122, 12, 73, 47, 32, 223, 121, 53,
  -29, 58, 84, 127, 143, 86, 371, 11]

def fractionalNearFrameSubtreeG2R0534LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0534Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0534LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
