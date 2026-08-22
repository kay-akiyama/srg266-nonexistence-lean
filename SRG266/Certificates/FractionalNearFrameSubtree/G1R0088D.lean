import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0088`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0088Mask : ℕ := 936549589781580

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0088Witness : Array ℤ :=
  #[0, 144, -225, -315, -86, 30, 95, 234, 3, 202, 9, -136, 0, -170, 6, 164,
  88, -145, -72, -172, -89, -274, -221, -3, 233, 270, 225, -75, -130, -352,
  -368, -198, -129, 34, 55, 106, -6, -31, 248, 1, 188, 344, -21, -121, -76,
  87, 261, 232, -139, -66, 18, 34, -109, -265, -276, -333, -94, 173, -216,
  94, 49, 0, -231, 50, 49, 347, -121, -295, -175, 192, 272, -17, -201, 77,
  280, 95, 87, 195, -147, -213, 285, 232, -93, 114, 136, 190, 303, 177, 118,
  77, 206, 259, 260, 110, -34, 66, 19, -38, 13, 127, 63, 41, -91, 193, 110,
  5, 116, -4, 166, -65, 117, -102, 243, -158, 28, -123, 218, -54, 29, 229,
  -33, 424, -399, 84, 37, -102, 52, -5, 203, -64, 135, -40, -157, 105, 100,
  -9, -217, -94, -158, 83, 102, 0, -203, 86, -185, 26, 0, 7, -204, -94, -84,
  253, 102, 240, 74, 27, -239, 208, -19, -252, 358, 27, -47, -112, -289,
  -264, -227, 490]

theorem fractionalNearFrameSubtreeG1R0088_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0088Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0088Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0088Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0088_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0088LowerBoundTable : List ℤ :=
  [-56, -181, 172, 332, 400, 273, 49, -36, -193, 12, 511, 306, 10, 336, 10,
  -330, 11, 1485, 249, -538, 337, 1039, 380, -180, 810]

def fractionalNearFrameSubtreeG1R0088LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0088Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0088LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
