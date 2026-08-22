import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0458`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0458Mask : ℕ := 5795158120641192

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0458Witness : Array ℤ :=
  #[22, 14, 61, 10, 30, -29, 14, 20, -23, 2, -21, -63, -14, 2, 18, -16, 12,
  59, -18, -3, 30, 9, 14, 15, 16, -73, -46, -2, 23, -21, -19, 15, 10, 0, -5,
  22, 15, 20, -68, -35, -18, -8, -29, 8, 21, 11, 14, -20, -15, 19, 29, 23,
  -19, -25, 8, -13, -7, 16, -16, 4, -16, -8, 30, -26, -41, 20, 11, 27, 26,
  32, 41, -27, -34, -61, 2, -39, -5, 31, 3, -3, -6, 40, 16, -56, -11, 6, 19,
  3, -1, 20, -15, 41, -55, 0, -28, -21, 33, 11, -7, -45, -36, 43, 0, 16, -7,
  -10, -4, -11, 35, 5, -22, 27, -1, -2, -2, 32, 9, 6, -42, -25, 54, 2, 20,
  -23, -5, -25, -8, 76, 0, -22, -15, 12, -31, -20, -8, 11, 6, -8, 21, -5,
  -38, -15, -16, -30, -13, -35, 52, -22, 12, -2, -71, -11, 58, -8, 2, 27,
  65, -30, 11, 4, -12, 62, 11, 21, 18, 40, -33, -4]

theorem fractionalNearFrameSubtreeG2R0458_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0458Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0458Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0458Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0458_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0458LowerBoundTable : List ℤ :=
  [-33, 26, -53, -7, 2, 2, 1, 3, 39, -33, 42, 10, 11, 128, -171, 43, -70,
  -27, 113, 10, 164, 40, 30, 76, -139]

def fractionalNearFrameSubtreeG2R0458LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0458Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0458LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
