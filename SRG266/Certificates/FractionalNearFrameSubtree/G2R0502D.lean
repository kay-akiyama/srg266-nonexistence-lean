import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0502`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0502Mask : ℕ := 5811566036562724

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0502Witness : Array ℤ :=
  #[11, -115, -145, -86, -32, 46, 29, 42, 58, 8, 79, 14, 29, 90, -54, -20,
  -7, -17, -67, 2, -8, 106, 19, -43, 66, -42, 94, 7, 26, -3, 171, 96, 145,
  -65, 55, -52, -9, -91, 67, -61, 80, -57, -53, -29, -1, -39, -49, -22, 110,
  -4, 10, 42, 53, 70, 52, 20, -69, 4, 51, -70, 15, 44, 23, -4, 139, 48, 171,
  36, -3, 49, -145, -6, 21, -69, -51, 29, 32, -16, 23, -82, 39, 5, -34, -18,
  19, 10, 15, -37, 31, 56, -25, 7, 5, 42, -17, -1, -12, 25, -12, -120, 1,
  16, 1, 0, 30, -52, -40, 20, -62, 32, -5, 6, -38, -5, -102, 81, -4, 49, -1,
  23, 31, 52, 86, 129, -68, -74, -48, 31, -55, 75, 23, 83, -33, -34, 30, 9,
  49, -7, 5, -127, -102, -48, 104, 28, 78, -22, 31, 3, 5, -61, 22, 39, -66,
  -6, -45, -22, 49, -42, -91, -2, -78, -40, -58, 23, 41, 3, 11, 47]

theorem fractionalNearFrameSubtreeG2R0502_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0502Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0502Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0502Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0502_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0502LowerBoundTable : List ℤ :=
  [-25, -52, 93, -47, 80, 1, 2, 137, 1, 196, 4, 89, 126, 24, 129, 128, 316,
  8, -69, 217, -160, 262, 9, 96, 9]

def fractionalNearFrameSubtreeG2R0502LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0502Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0502LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
