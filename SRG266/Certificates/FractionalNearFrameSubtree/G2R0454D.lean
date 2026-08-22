import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0454`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0454Mask : ℕ := 5794668861637196

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0454Witness : Array ℤ :=
  #[17, -25, 57, 12, 61, -35, 47, 44, -20, 51, -34, -27, -72, 13, -80, -19,
  2, 6, -1, 91, 39, -8, -18, 6, -17, -58, 50, -27, -13, 38, -1, -13, -9, 45,
  17, 12, 16, -10, -42, -22, -93, 28, -25, -34, 11, 29, -52, 26, -34, 38,
  -32, 19, -14, 86, -19, -21, 10, -7, 15, 33, 4, 40, -37, -57, -8, -31, 8,
  5, 19, 1, 32, -6, -10, -36, -33, -47, 0, 42, 47, 53, 9, -60, -106, 17,
  -139, 54, -15, 19, 8, -9, -7, 8, 48, 21, -3, 33, -23, 50, 50, 1, 35, -21,
  7, -12, -43, -19, -35, -18, -5, -15, -20, -13, -26, 57, -3, -31, 7, 5,
  -16, -8, -67, -1, -5, -28, 15, -26, 36, -26, 18, -17, 9, -14, 10, -14, 10,
  -26, -58, 67, -37, -7, -84, 27, 12, 8, 24, -50, -10, -30, 57, 87, 28, 51,
  51, -29, 4, -26, 12, -8, -125, 21, 43, 63, 16, 23, 21, -11, 19, -8]

theorem fractionalNearFrameSubtreeG2R0454_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0454Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0454Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0454Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0454_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0454LowerBoundTable : List ℤ :=
  [-86, -4, -141, 1, 79, 65, 1, 7, -28, 142, 66, 8, 10, 8, -136, -214, 45,
  9, 8, 51, 10, -71, 14, 59, 10]

def fractionalNearFrameSubtreeG2R0454LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0454Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0454LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
