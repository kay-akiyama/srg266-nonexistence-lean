import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0057`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0057Mask : ℕ := 727788199463433

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0057Witness : Array ℤ :=
  #[38, 8, 43, 34, 14, 59, 7, -17, 52, -20, -6, -29, 0, -22, -86, 0, -30,
  -9, 46, -23, -29, 24, 75, 22, -26, -74, -65, -21, -11, 17, -28, 63, 34,
  23, 7, 3, 24, 11, 0, -27, 12, 23, 32, 5, -97, -27, 31, -30, -38, -25, 23,
  -4, -2, -4, -24, 57, -1, -62, 13, -21, -16, 34, 8, -45, -31, 58, 81, 16,
  27, 30, -20, -26, 10, -21, -41, -6, -112, -1, 41, -21, 23, 82, 43, 9, 38,
  38, -43, 54, 52, 11, 45, 14, 7, 2, -7, -52, 46, -43, 15, 9, 28, -29, 14,
  1, -41, -16, -77, -6, 7, 44, 20, 14, -5, 26, 51, 68, -22, -115, -24, -23,
  2, -43, -5, -17, -28, 51, 36, -32, 3, -10, -26, 32, 13, 60, -33, 5, -59,
  7, -79, 3, -44, 10, -17, -17, 2, -34, -2, -1, -10, 26, 6, 28, 37, 11, 1,
  -31, 24, 30, 31, 58, 77, -12, 65, 43, -30, -9, -2, -8]

theorem fractionalNearFrameSubtreeG1R0057_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0057Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0057Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0057Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0057_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0057LowerBoundTable : List ℤ :=
  [-14, 8, -21, 2, 108, 26, 1, 3, 20, 40, 91, -14, -36, -86, 76, -71, 11,
  72, 77, 181, 202, 100, -149, 195, -38]

def fractionalNearFrameSubtreeG1R0057LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0057Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0057LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
