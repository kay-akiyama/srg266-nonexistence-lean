import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0248`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0248Mask : ℕ := 5177448468300562

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0248Witness : Array ℤ :=
  #[0, -14, 63, 41, 46, -29, -2, 0, 10, 28, -74, 33, -48, 79, 88, -29, -1,
  -22, -1, -22, -48, 64, 30, 54, -4, 12, -30, -85, -24, 32, 36, 20, 6, -8,
  15, -17, -5, -8, 14, 40, 45, -11, -29, -16, 6, -47, -24, -22, -48, -2,
  -13, -1, -37, 71, 41, 18, 0, 6, 49, -35, -43, 9, 34, 26, 19, 70, 19, -9,
  87, 56, 14, 7, 40, -15, -11, 10, -10, -11, -6, 37, 25, -35, -14, -17, 12,
  88, 2, 4, 4, -17, 55, -39, -8, 45, 24, 6, 22, -15, -11, 10, 51, 78, 14,
  16, 33, 38, 13, 29, -16, -33, -25, -108, 54, 73, -2, -6, -5, -8, -6, 14,
  21, -7, 0, -11, -33, 13, 7, 21, -33, 14, 32, -17, 62, 8, 5, 25, 63, 0, 30,
  37, 13, -19, -34, 17, 45, -29, -5, 38, 15, -1, -32, 59, -43, -8, 51, -6,
  -18, -17, 9, 29, -39, -4, 61, 12, -22, -6, 9, -77]

theorem fractionalNearFrameSubtreeG2R0248_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0248Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0248Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0248Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0248_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0248LowerBoundTable : List ℤ :=
  [23, 3, 106, 69, 37, 20, 23, 217, 78, 41, 169, 129, 34, 40, 256, 150, -29,
  34, 10, 394, 186, 57, 150, 72, 77]

def fractionalNearFrameSubtreeG2R0248LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0248Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0248LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
