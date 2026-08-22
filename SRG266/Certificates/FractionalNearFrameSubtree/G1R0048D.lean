import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0048`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0048Mask : ℕ := 554580980646104

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0048Witness : Array ℤ :=
  #[-36, -25, 31, -98, -103, 87, 52, 72, 83, -38, -2, -35, 61, -17, 1, 12,
  38, -51, -67, 62, 30, 43, -80, -107, 46, 1, 89, 34, -37, -22, -51, -44,
  55, 177, 29, -36, 29, 68, 112, -13, 0, 80, 81, 0, 16, 88, 96, 85, -25, 4,
  -46, -33, 4, -33, 3, 15, -26, -12, -75, 117, -11, 70, 95, -125, -123, 41,
  64, -95, 120, 30, -35, -1, 19, 53, -13, -7, -89, 117, -18, -55, 3, 33, 50,
  34, 89, -21, -27, -11, 90, 55, 94, 4, 55, 37, -94, 27, -20, 10, 4, 77,
  100, 37, 70, 25, -72, 40, -6, -54, -18, 0, -63, -69, -56, 49, 46, -30,
  -31, -24, -43, 46, -25, 30, 22, 40, -55, 9, -132, 61, -34, -22, 77, 39,
  -39, 89, -16, -64, 106, 51, -51, -105, 18, 17, 50, -19, -33, -78, 118, 74,
  -33, -53, -38, 22, -20, 29, 7, 43, -8, 44, 84, -36, 25, 54, 23, 28, 12,
  -43, 12, -62]

theorem fractionalNearFrameSubtreeG1R0048_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0048Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0048Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0048Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0048_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0048LowerBoundTable : List ℤ :=
  [50, 2, 22, 3, 169, 193, 217, 218, 87, 232, -194, 71, -93, 352, 168, 9,
  81, 104, -110, 9, 102, 9, 391, 11, 330]

def fractionalNearFrameSubtreeG1R0048LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0048Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0048LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
