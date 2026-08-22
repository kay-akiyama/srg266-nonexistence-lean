import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0411`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0411Mask : ℕ := 5742498390788528

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0411Witness : Array ℤ :=
  #[15, -28, -86, -6, -5, -2, 72, 9, -25, 69, 17, -10, -10, 49, 50, 0, 6,
  -15, 41, 93, 17, 58, 43, -38, 40, -66, -9, -35, 54, 86, -12, 24, 17, 42,
  -33, 23, 41, 31, -6, -75, -26, -28, -5, -59, -61, 1, -44, -38, 63, 30, 63,
  73, -13, 91, 30, -104, 108, 47, -33, 72, 59, 26, 99, 81, 90, -3, -49, 45,
  63, 96, 50, -69, 53, -26, 34, 52, -31, -4, 26, -37, 11, 108, -5, -111, 22,
  61, -42, -48, -91, -12, -53, -44, -31, 52, 0, 11, -52, 7, -55, 79, 53, 15,
  30, -59, 45, 66, 34, -39, 6, 23, -25, -17, 30, 27, 22, 28, 0, -76, 18,
  -34, -19, -21, 85, -26, -17, -17, 16, -7, 17, 7, 11, 61, 87, -2, 47, 1,
  -35, -29, 54, 14, 1, 87, -129, 55, 106, -14, -9, -39, 52, -112, -3, -103,
  14, -1, -6, 38, 31, 50, 19, 6, -1, 46, -17, 16, -74, 26, 41, 34]

theorem fractionalNearFrameSubtreeG2R0411_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0411Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0411Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0411Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0411_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0411LowerBoundTable : List ℤ :=
  [82, 22, 207, 54, -18, 37, 214, 158, 112, 263, 291, -108, 69, 312, 218,
  157, 312, 10, -19, 116, 8, -27, 166, 193, 11]

def fractionalNearFrameSubtreeG2R0411LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0411Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0411LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
