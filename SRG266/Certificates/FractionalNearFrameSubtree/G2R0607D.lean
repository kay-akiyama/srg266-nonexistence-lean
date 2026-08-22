import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0607`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0607Mask : ℕ := 7048678502798866

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0607Witness : Array ℤ :=
  #[12, -14, 21, -28, -49, 13, -27, -27, 7, 0, -2, -44, 88, -18, -73, -3,
  -14, 86, 31, 17, 5, -28, -61, 32, -25, -60, 32, -60, 6, 22, -38, -28, -28,
  -27, 21, 36, 9, 38, 59, 3, 24, 2, -44, -10, -3, -41, 22, -8, -25, 49, -49,
  37, 63, 21, 3, -30, 30, 26, -6, -1, -85, -75, 28, -62, -68, 60, 7, -28,
  -9, -23, -15, -26, 11, -20, -22, 8, 33, 24, 27, 38, -100, 42, 14, 12, 5,
  -18, -33, -38, 28, 18, 33, -4, -17, 7, -27, -14, -23, -9, 2, 13, 0, 6, 28,
  8, -50, -3, 26, -43, 9, 53, 20, -37, 5, -49, 0, 25, -48, 26, 63, 33, 16,
  35, -74, -58, 27, -60, -46, 45, -42, -35, -39, 37, -9, 39, -57, -11, 22,
  24, -14, -15, -26, 29, -19, 15, 6, 37, -11, 15, 36, -33, 30, -60, -42, 14,
  40, 2, -58, -126, 45, 62, -12, 30, 46, 48, 4, -108, -23, -25]

theorem fractionalNearFrameSubtreeG2R0607_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0607Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0607Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0607Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0607_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0607LowerBoundTable : List ℤ :=
  [-100, -30, -83, -97, 2, -39, 2, -68, -63, -54, 57, 4, -120, 157, 153, -4,
  -107, -37, -20, -262, 65, 104, 11, -18, -61]

def fractionalNearFrameSubtreeG2R0607LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0607Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0607LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
