import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0033`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0033Mask : ℕ := 521900574548556

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0033Witness : Array ℤ :=
  #[-37, 26, -29, -32, -113, -50, -5, -31, 66, -2, 107, 116, 56, 4, -11, 17,
  -49, -49, -148, 111, 0, -8, -3, -14, 78, 32, 65, 52, -12, 50, 74, -27,
  -57, 52, 21, 43, -79, -76, -86, 91, -55, 0, -9, 74, 59, 40, 167, -71, -34,
  36, -27, 31, -32, -86, 37, 86, 65, -115, -33, 32, -14, -46, -43, -16, -17,
  -12, -10, -100, -23, 3, -24, 0, 4, 47, -6, -149, -1, -17, -41, -27, 2, 52,
  -41, -7, 107, 36, -15, -32, -144, -90, 4, -44, 22, -36, 11, 153, -48, 37,
  21, 37, 6, 49, 102, 51, 59, 201, 139, 213, 188, -37, 131, 49, -14, -152,
  -47, -180, -80, -55, 16, -59, 84, 73, 39, -16, 24, 3, 0, -10, 1, 56, 3,
  45, -14, 74, -57, -27, 30, 54, 48, 65, 48, 138, 1, 66, 39, 84, 35, -32, 6,
  69, 73, 56, 12, 6, -60, -51, -5, 93, 26, -78, 27, -25, 40, 28, -19, 1, 23,
  39]

theorem fractionalNearFrameSubtreeG1R0033_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0033Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0033Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0033Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0033_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0033LowerBoundTable : List ℤ :=
  [24, 298, 78, -61, 265, 3, 168, 4, 84, 202, 591, 108, 370, 83, 264, -54,
  -118, -50, 10, 9, 148, 411, -174, 228, 215]

def fractionalNearFrameSubtreeG1R0033LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0033Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0033LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
