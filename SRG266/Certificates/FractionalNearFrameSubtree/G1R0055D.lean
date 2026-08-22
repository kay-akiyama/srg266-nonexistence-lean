import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0055`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0055Mask : ℕ := 688120954872073

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0055Witness : Array ℤ :=
  #[-49, -101, -57, -53, -100, -70, 55, -9, 67, -27, -9, 4, 72, 84, 28, 96,
  43, 0, -8, -13, -33, -3, 15, 75, 39, 39, 61, 25, -53, -44, -27, -25, -38,
  -15, -47, -18, -16, 87, 42, -1, 6, 8, 17, -16, -2, 3, 24, -3, 70, 9, 6,
  39, 37, 49, 8, 0, -22, 18, -8, -1, -8, 2, 47, -1, -15, -5, 28, 87, 54,
  -34, -39, -2, 67, 0, -66, -5, 2, 69, 18, 13, 31, -8, 14, 38, -6, 18, -88,
  11, -18, -41, 3, -12, -25, 43, -16, -6, 65, 55, 7, 31, 5, 10, -10, 0, -12,
  -36, -24, -96, -99, -101, -15, -85, -60, -5, 27, 72, -34, 27, -19, -31,
  29, -1, 19, -69, 17, 11, -15, 39, 6, 97, 16, -80, 26, -44, 59, -70, -58,
  -74, -41, 9, 10, 5, 48, 37, 24, 32, 59, 42, 7, -9, -18, 36, 4, 17, 18,
  -48, 50, 7, -1, -68, -4, 5, 83, -60, -72, 5, 11, -9]

theorem fractionalNearFrameSubtreeG1R0055_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0055Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0055Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0055Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0055_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0055LowerBoundTable : List ℤ :=
  [-20, -39, -27, 64, 64, 76, 1, 3, 35, 105, 50, 58, -123, -4, -51, 91,
  -126, 91, 58, 103, 9, 10, -21, 148, -148]

def fractionalNearFrameSubtreeG1R0055LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0055Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0055LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
