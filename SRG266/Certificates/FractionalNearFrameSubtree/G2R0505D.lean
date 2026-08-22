import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0505`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0505Mask : ℕ := 5811626436889192

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0505Witness : Array ℤ :=
  #[34, 60, -52, -33, -20, -27, -7, -4, -60, 14, 67, 49, 11, 42, 60, 65,
  -64, -44, -48, -22, 3, -67, 7, 8, 39, 29, 19, -12, 23, 17, -38, -17, 1,
  -6, 22, 104, 0, -41, -70, -25, 4, -1, -1, 33, 34, -11, 3, -101, 16, -6,
  -8, -42, -33, -21, -16, 2, 21, 29, 9, 7, 9, 2, 28, 37, 58, -7, 23, 28,
  -50, 49, -35, -1, 53, -11, -16, 23, 0, -12, 10, -5, -44, 10, 0, -20, 17,
  -12, -15, 25, 49, 9, 7, 12, 23, 4, 12, 25, 41, 11, -46, 21, -24, 14, 7,
  11, -25, 33, -14, 32, -11, 39, 1, 28, 37, 8, 2, -35, -5, 12, 34, 48, 31,
  -28, -64, -1, 10, 56, -36, 26, 43, 31, -15, 30, 25, -49, 42, -25, 57, -60,
  58, 59, 10, 62, 13, 19, -30, 0, -23, -12, -6, 40, 55, -69, 11, 3, 30, -26,
  15, 6, 33, 42, 56, 41, 28, -14, 49, -1, -15, -1]

theorem fractionalNearFrameSubtreeG2R0505_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0505Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0505Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0505Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0505_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0505LowerBoundTable : List ℤ :=
  [32, 107, 83, 1, 2, 78, 83, 1, 141, 190, 158, 238, 186, 50, -20, -6, 85,
  32, 8, 50, 164, -68, -10, 218, 177]

def fractionalNearFrameSubtreeG2R0505LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0505Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0505LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
