import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0536`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0536Mask : ℕ := 6796858643913249

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0536Witness : Array ℤ :=
  #[60, 59, 82, 102, 109, 83, 44, 82, 61, 34, 70, 55, -139, -115, -111,
  -131, -136, -97, 14, -93, -78, -40, 0, 15, -81, -17, -90, -24, 98, 94,
  132, 165, 40, 20, 60, 30, -28, -12, 1, -2, 3, 8, -13, -45, 13, 0, 15, -8,
  1, 16, -22, -11, -10, 5, -17, 1, 3, -27, -19, 16, -2, 1, 14, 10, 3, -5,
  -2, 1, 5, -9, -42, -23, 13, 11, 31, 23, 4, -29, 17, -5, -15, -25, -2, -5,
  2, -6, -24, -28, -42, -46, 10, -21, 26, -7, -1, 8, 15, -2, -24, 11, -3,
  25, 7, 0, 3, 5, -19, -25, -7, 47, 32, 19, 21, 21, 30, 30, 19, 5, -48, -8,
  -2, -9, 6, -11, 31, 14, 6, 0, 6, 11, -8, 0, 16, 6, -3, 9, 6, 12, -29, -24,
  -10, -6, -15, 1, 13, 0, 2, -1, 8, 23, -8, 22, -5, 14, 1, 13, 26, -11, -12,
  31, 13, 16, 3, 26, 8, -9, 36, 1]

theorem fractionalNearFrameSubtreeG2R0536_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0536Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0536Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0536Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0536_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0536LowerBoundTable : List ℤ :=
  [25, 53, 2, -50, 85, 86, 48, 3, 55, 142, 11, 9, 72, 77, -4, 2, 28, -98,
  47, 19, -18, 110, 125, 153, -58]

def fractionalNearFrameSubtreeG2R0536LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0536Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0536LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
