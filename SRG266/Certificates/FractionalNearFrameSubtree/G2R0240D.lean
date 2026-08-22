import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0240`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0240Mask : ℕ := 5109110443460881

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0240Witness : Array ℤ :=
  #[0, 54, 149, 33, 159, 61, -92, -100, -159, -56, -159, -22, -9, 94, 28,
  10, 72, 35, 161, -8, 43, 42, 37, -10, -9, 2, 3, 15, -6, -18, -30, -68,
  -101, -70, 102, 107, 48, 16, 46, 61, -242, -184, -48, -117, -46, 143, 190,
  -33, -2, 29, 69, -11, -15, -4, -37, 7, 12, -35, 50, 57, 37, 11, 31, 88,
  -29, -46, -2, -26, -69, -7, 17, 18, -22, 2, -18, -23, -23, -19, -21, -33,
  0, -39, 34, -34, -14, 2, -31, 0, 48, -28, 34, -13, 26, -13, 4, -20, 24,
  -39, -29, -12, 40, 24, -20, -32, 3, 10, -38, 25, -31, 2, -8, 8, -8, 23,
  35, 63, 43, 87, -49, -100, -10, 13, 36, -5, -34, -38, -22, 115, -107, 68,
  67, 68, -61, 8, -25, -40, 8, 20, -16, -28, 38, -31, -8, -9, -11, -19, -19,
  -6, 44, 33, -18, -29, -13, -33, -8, 16, 31, 47, 32, 55, 26, 36, -12, 0,
  38, 14, 18, -39]

theorem fractionalNearFrameSubtreeG2R0240_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0240Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0240Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0240Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0240_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0240LowerBoundTable : List ℤ :=
  [-25, -24, 2, 2, 91, 123, 2, 1, 39, 9, 187, -34, 10, 37, 11, -116, 239,
  -53, -20, -46, 23, -86, 198, 259, -206]

def fractionalNearFrameSubtreeG2R0240LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0240Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0240LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
