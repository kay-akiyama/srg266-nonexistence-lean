import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0016`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0016Mask : ℕ := 676942415088137

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0016Witness : Array ℤ :=
  #[0, 64, 38, -10, 128, 82, 87, 101, 34, 49, 17, 1, -62, -45, -145, -102,
  -165, -139, 1, -158, -60, -95, -96, 56, -42, -36, -72, -70, 164, 80, 188,
  120, -64, 29, 38, 21, 11, 97, 31, 101, -105, -1, -120, -13, -49, -129,
  -133, 47, 109, 36, 70, 169, -43, 55, 89, 105, 136, -36, 39, 10, -41, 29,
  -50, -66, -2, 1, -15, 22, -8, 25, 57, -9, 46, 24, 67, -17, -44, 29, 54,
  19, -19, 24, 0, -32, 1, 70, 41, 26, 32, -35, -47, -6, -9, 81, -14, -60,
  11, 37, -1, -22, -27, 17, -14, -18, -41, 52, 89, -8, 1, 90, 11, 11, -79,
  25, -30, -75, -90, 12, -47, 6, -94, -75, 17, 21, -76, 4, 2, 52, -57, 30,
  -32, -33, -82, 4, 87, -37, 5, 25, -16, 27, 43, -81, -17, -18, 61, -63, 22,
  15, 49, 58, 0, -125, 22, -56, 58, -22, -28, 26, 44, 59, 11, -58, 20, -14,
  -28, 7, 36, 21]

theorem fractionalNearFrameSubtreeG2R0016_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0016Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0016Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0016Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0016_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0016LowerBoundTable : List ℤ :=
  [-67, -97, 49, 4, 1, -63, 185, 82, 88, 10, 222, 100, 46, 196, 226, 10,
  -290, 49, -53, 10, 10, 11, -109, 145, 24]

def fractionalNearFrameSubtreeG2R0016LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0016Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0016LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
