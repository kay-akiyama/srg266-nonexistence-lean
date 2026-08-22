import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0213`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0213Mask : ℕ := 2365765379399777

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0213Witness : Array ℤ :=
  #[31, 120, 144, 131, 0, 54, -231, -126, -109, 72, -53, -17, 26, -29, 36,
  33, -34, 40, -69, 97, 103, 24, -30, 65, -111, 57, 13, -4, 9, 26, 31, 163,
  -50, 71, 40, 82, 97, -71, 0, -57, 34, -65, -53, -53, 50, 20, -21, 51, 3,
  4, 0, -49, 23, 25, -79, 40, -27, -38, 13, 93, -139, 121, 87, 29, 0, -11,
  -39, 13, -25, 76, -32, -58, 38, -24, -20, -5, -57, -42, -9, 55, -70, 35,
  30, -45, -10, 32, -33, -30, -17, -55, 10, -73, 4, -31, 55, 99, -14, 196,
  56, -17, -83, 85, -68, -25, -4, 5, -8, 155, 0, -102, -21, 37, -30, 131,
  10, 159, 19, 96, -132, -73, 141, 95, 101, -1, 82, 41, -45, 50, 10, 84, 28,
  -23, 52, 4, 103, -22, 33, 32, 65, -33, -32, -113, -15, 34, -37, -22, 106,
  -20, -55, 37, 19, 72, 25, 103, 49, -2, -14, -57, 16, -41, -14, -7, -72,
  -27, -6, -29, 7, -263]

theorem fractionalNearFrameSubtreeG2R0213_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0213Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0213Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0213Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0213_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0213LowerBoundTable : List ℤ :=
  [-3, 51, -93, 1, 250, 86, 15, 2, 2, 219, 177, 329, 4, -11, -55, 85, 181,
  297, 512, 93, 75, 321, 375, 395, -69]

def fractionalNearFrameSubtreeG2R0213LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0213Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0213LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
