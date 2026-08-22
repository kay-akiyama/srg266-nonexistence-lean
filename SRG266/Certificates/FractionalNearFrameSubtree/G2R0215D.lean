import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0215`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0215Mask : ℕ := 2365769324022305

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0215Witness : Array ℤ :=
  #[-172, -99, -25, -28, -86, -64, 7, -18, 39, 25, 80, 39, 43, 20, 92, 59,
  55, 119, 50, -33, 22, 34, -41, -1, 26, 17, 15, 26, -27, -13, -67, 55, -46,
  -15, 43, -21, -51, 0, -7, 12, 17, -21, 82, -4, 67, -45, -8, -17, 52, -13,
  0, -13, 76, 50, 55, 20, 26, -11, -20, 10, -52, 57, 24, 4, 28, -11, -1, 2,
  37, -44, 19, 30, -27, 34, 3, 3, -3, -28, 9, 1, 8, -34, 8, 8, 13, -16, 12,
  -4, 29, 9, 7, 6, 14, 47, 16, 89, 44, -5, 16, -14, -5, 12, -25, 32, -30,
  39, 50, -6, -2, 39, 66, -33, -45, -47, 59, 40, -36, 16, -12, 9, -4, -46,
  3, 15, -11, 8, 20, 38, -39, 22, 37, 2, -16, -18, 10, 8, 9, -5, -1, -6,
  -21, 54, -20, 4, -6, -49, 84, -13, -14, -11, -38, -21, -51, 79, 0, -14,
  10, 14, -64, -31, -19, -18, -11, -10, 22, -43, 50, -137]

theorem fractionalNearFrameSubtreeG2R0215_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0215Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0215Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0215Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0215_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0215LowerBoundTable : List ℤ :=
  [19, -34, 1, 42, 114, 20, 2, 3, 51, -81, -14, 35, 44, 34, 111, 162, 140,
  71, 19, -5, 59, 156, 421, 128, 11]

def fractionalNearFrameSubtreeG2R0215LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0215Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0215LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
