import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0105`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0105Mask : ℕ := 959692500746642

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0105Witness : Array ℤ :=
  #[-99, 33, 22, -47, 100, 3, -76, -74, -58, -47, -55, 56, -38, 44, 38, 49,
  26, 112, 0, 49, 28, 24, 14, -8, -10, -22, -29, 32, 10, 51, -80, -31, -193,
  -33, -49, -18, -6, 9, 12, 26, 36, -6, 55, 80, 44, 56, -67, 8, 29, -4, -36,
  -71, -25, 54, 20, 57, -45, 43, -86, -95, -2, 83, -23, 82, -86, 25, 107,
  10, 109, 3, -14, -19, 23, -8, -11, 12, 22, -14, -48, 28, 11, 3, 27, 23,
  75, 36, -1, -31, -22, -13, -14, 14, 24, 43, -36, -10, 14, 47, -7, -5, 21,
  -10, -47, 21, 27, 14, 68, -13, -14, -29, 59, -15, -24, 0, -21, 31, 12, 77,
  3, -6, 51, 18, 1, -38, 33, -43, 0, -14, 54, 23, 44, -40, -14, 11, -22, 12,
  10, 42, 64, 8, 13, 34, -4, -35, -70, -51, 19, 1, -22, 15, 0, -62, -47,
  -12, 26, -24, 9, 45, 26, -8, -29, -19, 10, 30, 11, -5, -38, -46]

theorem fractionalNearFrameSubtreeG1R0105_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0105Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0105Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0105Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0105_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0105LowerBoundTable : List ℤ :=
  [-12, -22, 57, 37, 53, 159, -102, 3, 32, -57, 84, -31, 128, 213, 10, 96,
  109, 52, -101, 73, 10, 9, -40, 164, 48]

def fractionalNearFrameSubtreeG1R0105LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0105Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0105LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
