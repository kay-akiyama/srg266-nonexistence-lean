import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0139`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0139Mask : ℕ := 1039403209638228

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0139Witness : Array ℤ :=
  #[-39, 47, -28, -50, -17, 70, 92, 12, 82, 78, -6, -27, -41, -8, 0, 68,
  -35, 18, -23, 67, 27, 58, 7, 53, -20, -10, -21, -39, -10, 24, 14, 10, -61,
  -54, 11, 54, -38, -19, 100, 110, 116, 121, 7, -39, -11, 104, 106, -93,
  -160, -65, 92, 177, 132, 3, 42, 12, 26, 20, 102, -75, -85, 150, 92, -1,
  42, -71, 59, -13, 15, -11, 27, -23, 2, 38, -55, 83, 69, 67, 14, 46, 62,
  -63, 36, 49, 7, 16, -8, -13, 6, 70, 63, 11, 50, 1, -8, 27, 32, 66, 34, 71,
  42, 135, -11, 0, 11, -4, -11, 22, 9, 77, 36, -34, 66, -4, -5, 65, 23, 60,
  49, -13, -55, -21, -28, -32, 31, -31, -21, 72, 79, -14, -72, -124, 47, -7,
  -24, -39, -9, -6, -37, 10, -33, -53, 79, 13, 27, 17, -2, -24, 14, -63,
  -30, -26, 2, 179, 0, 132, 16, 2, 71, 25, -36, 49, 40, 2, 0, -19, -78, 22]

theorem fractionalNearFrameSubtreeG1R0139_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0139Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0139Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0139Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0139_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0139LowerBoundTable : List ℤ :=
  [154, 57, 287, 109, 151, 259, 237, 148, 104, -164, 227, 10, 218, 487, 530,
  274, 276, 187, 30, 336, 9, 357, 259, 240, 180]

def fractionalNearFrameSubtreeG1R0139LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0139Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0139LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
