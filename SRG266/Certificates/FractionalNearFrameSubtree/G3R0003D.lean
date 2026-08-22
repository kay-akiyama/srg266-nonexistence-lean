import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0003`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0003Mask : ℕ := 261473519128721

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0003Witness : Array ℤ :=
  #[-41, -42, 33, 51, -67, -31, -37, -22, -25, -46, -91, 19, 81, 75, 44, 54,
  16, 11, 77, -11, -69, 24, 16, 2, 8, -73, -33, -16, 16, 73, 32, -29, -14,
  -85, -69, -82, 31, 66, 0, -20, 70, -10, -39, 44, 52, 6, 28, -18, 24, -1,
  -37, 27, 44, -49, -70, -57, -41, -75, -21, -99, -1, 27, 94, 88, 66, 58,
  101, -6, -120, -31, -33, 12, -16, 14, -7, -47, -42, -1, -19, -30, 10, 49,
  34, 6, -12, -39, 69, 56, -73, 26, 19, 46, -31, -1, 0, -10, 7, 6, 13, 46,
  29, 4, 34, 2, -9, 16, 38, 13, -46, -35, -18, 62, 54, -14, -13, 1, -38, 65,
  16, 16, -73, -42, 27, 57, -24, 22, 39, 7, -4, -49, -82, 57, -64, 10, 35,
  16, 20, -72, 51, -33, -28, 25, 16, 4, 1, -30, 53, 5, 33, -44, -21, 20, 29,
  -58, -12, 42, 67, 68, -14, -94, -70, 34, 40, -25, 11, -65, 81, 65]

theorem fractionalNearFrameSubtreeG3R0003_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0003Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0003Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0003Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0003_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0003LowerBoundTable : List ℤ :=
  [-77, -5, -25, -50, 58, 21, 1, -18, 12, 10, 71, 81, 247, 21, -69, 19, -58,
  155, 165, -130, 9, 10, 152, 209, -6]

def fractionalNearFrameSubtreeG3R0003LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0003Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0003LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
