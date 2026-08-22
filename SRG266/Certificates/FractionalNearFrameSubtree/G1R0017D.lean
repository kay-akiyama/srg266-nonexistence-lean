import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0017`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0017Mask : ℕ := 273597748138129

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0017Witness : Array ℤ :=
  #[-70, -67, -53, -5, 27, -15, 33, -4, 101, 62, 0, -11, 68, -12, 33, 35,
  22, 64, 61, 39, 16, 37, 80, -45, -43, -40, -43, -39, 5, 34, -3, 25, 0,
  -80, -14, -61, -4, 36, 48, 71, -64, -5, 7, -9, 28, -16, 89, 23, -29, -21,
  22, 23, -31, -60, 55, 11, 34, -53, -42, 47, -45, -4, -67, 38, 55, -40,
  -32, 52, 96, -45, -19, -34, 80, 48, 78, 30, -51, -20, 3, 38, 65, -20, 1,
  20, 15, -78, -53, -51, -1, -55, 13, 32, -84, 78, -70, 66, -62, 52, -22,
  -21, -93, -86, -13, -34, 54, 59, 22, 32, 32, 49, -69, 10, -13, 48, 0, 58,
  -40, -19, -25, 104, 74, -24, 14, 63, -22, 16, -74, 63, 55, 5, 27, 3, 1,
  -15, 27, -20, -6, -14, -23, 61, 23, -15, -9, -6, -39, 25, -18, -3, 1, -21,
  42, 21, -12, 5, -16, 4, -8, -36, 1, 15, -12, -36, 9, -45, -39, -5, -41,
  -85]

theorem fractionalNearFrameSubtreeG1R0017_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0017Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0017Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0017Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0017_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0017LowerBoundTable : List ℤ :=
  [-49, -29, -155, 2, 151, -79, 1, 2, 126, 54, -152, 152, 249, 15, -141,
  -206, 25, 220, 40, 118, 234, 140, 75, 288, 8]

def fractionalNearFrameSubtreeG1R0017LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0017Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0017LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
