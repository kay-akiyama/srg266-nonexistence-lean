import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0253`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0253Mask : ℕ := 5355637007027474

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0253Witness : Array ℤ :=
  #[4, 16, 16, -2, -16, 25, -15, -30, 32, 18, 27, -68, -36, 0, -16, -44, 15,
  -8, 2, 34, -34, -18, -18, -6, 11, -18, -34, 0, 40, -31, 15, -14, 24, 35,
  -7, -20, -78, -18, 47, 13, -9, 24, 0, 11, -32, -46, -83, 71, 0, 70, 54,
  26, -6, -10, -21, 41, 0, 50, -141, 16, 7, 4, -29, 1, 20, -22, -20, 10, 19,
  26, -121, 17, 32, 69, -19, -26, -19, 35, -47, -104, 66, 22, 18, -18, -22,
  -11, 74, 33, 29, -29, 3, 54, -1, 52, 65, -35, 11, 10, 48, 21, -82, -26,
  -35, 16, 68, -61, -77, -4, 35, 48, 63, 9, 130, 55, -61, -30, -62, -61,
  -32, 0, 5, 1, -26, 110, 37, -16, 35, 14, 5, 23, 37, -29, -18, -1, -75, 61,
  -47, 34, -20, 13, 27, 75, 22, -7, 29, -32, -63, -51, -10, -16, -12, -5,
  -26, -55, -16, 43, -40, 62, 4, -16, 10, -8, -14, -9, 74, 28, -38, 24]

theorem fractionalNearFrameSubtreeG2R0253_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0253Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0253Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0253Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0253_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0253LowerBoundTable : List ℤ :=
  [-54, 11, 1, 41, -41, -26, -42, 1, -26, 131, 52, 97, 296, 45, -77, 162,
  83, 180, -110, 100, 70, -69, -75, -80, 103]

def fractionalNearFrameSubtreeG2R0253LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0253Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0253LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
