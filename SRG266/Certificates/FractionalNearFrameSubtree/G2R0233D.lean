import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0233`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0233Mask : ℕ := 5090587121537545

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0233Witness : Array ℤ :=
  #[56, 28, 43, 74, 0, 72, 42, 77, 59, 87, 69, 93, -137, -132, -134, -97,
  -80, -85, 45, -81, 32, -142, 24, 44, -80, -79, 18, 23, 71, 72, 151, 77, 1,
  17, 29, 10, -13, -8, -25, -21, -4, 42, 1, -63, -7, 4, -47, -6, 13, 17, 4,
  50, -21, 47, -5, -2, -54, 23, -6, -8, 12, 7, 11, -11, -25, -12, 2, -35, 5,
  1, -3, -6, 27, -4, -37, -6, 25, -9, -12, -7, -6, 7, 3, -18, -34, 39, 30,
  43, 17, 36, -4, -1, -1, -6, 54, -10, 12, -4, -6, 11, 7, -13, 6, -36, -21,
  -4, 17, 12, 28, -50, -43, -3, 35, 9, -35, 27, 15, 0, -23, 2, 13, -6, -39,
  15, -16, -10, 35, -41, 48, 7, 13, -37, -3, -6, -13, -13, 1, -40, -1, 4, 2,
  14, -5, -38, -15, 0, -35, 35, 1, 10, 8, -1, 10, -38, -29, -4, 24, 15, 0,
  71, 0, 54, -14, 18, 51, 25, 49, -14]

theorem fractionalNearFrameSubtreeG2R0233_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0233Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0233Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0233Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0233_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0233LowerBoundTable : List ℤ :=
  [8, 22, 3, -47, 130, 51, 2, 1, 17, 46, 46, -12, 10, 10, -2, -28, -4, 60,
  21, 116, 15, 123, 191, 14, -48]

def fractionalNearFrameSubtreeG2R0233LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0233Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0233LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
