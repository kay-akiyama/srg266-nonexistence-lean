import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G4R0034`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0034Mask : ℕ := 5434388141162836

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0034Witness : Array ℤ :=
  #[-141, -40, -105, -213, -299, 90, -91, -72, 107, -311, -57, 0, -11, 418,
  23, 0, -170, 5, 0, 116, -171, 128, -129, -43, -3, -206, 385, 80, -33, 109,
  -101, -230, 7, -222, 463, 96, 228, 143, 58, 233, -35, -109, 0, -132, 171,
  217, 63, -140, 106, 2, 1, 27, -31, -240, 0, -72, -4, 106, 135, 27, 205,
  33, -17, -48, -57, -144, -24, 173, -116, -226, 18, -226, -165, 159, -171,
  118, 267, -31, 8, -87, -65, 87, 267, -89, -8, 120, 65, -56, -101, -107,
  317, -135, -3, 124, 248, -139, 86, -89, 18, 459, 70, 229, 14, 135, 355,
  119, 313, -191, -4, -279, -238, 44, -81, -311, -245, -92, 154, 182, 244,
  -255, 5, -16, -11, 140, -82, 115, 72, -240, 68, 196, -152, 20, -47, -248,
  -200, 329, 14, -37, 36, 234, -149, 139, 16, 320, -23, -38, 383, 246, 171,
  179, 35, 26, 222, 9, 122, -179, 9, -77, 191, 81, -164, 78, 56, 146, -25,
  -94, 41, -26]

theorem fractionalNearFrameSubtreeG4R0034_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0034Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0034Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0034Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0034_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0034LowerBoundTable : List ℤ :=
  [-4, 274, 402, -57, 154, 358, 326, -266, -244, 1320, 681, 9, -781, 611,
  965, -409, 9, 158, 343, 762, 443, 360, 238, 827, 412]

def fractionalNearFrameSubtreeG4R0034LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0034Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0034LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
