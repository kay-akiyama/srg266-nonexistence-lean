import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0272`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0272Mask : ℕ := 5370946422149794

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0272Witness : Array ℤ :=
  #[44, -78, 16, -78, -5, 56, -105, -191, -123, -173, -165, 43, 88, 87, 134,
  11, 57, -171, -26, 1, -95, 0, -215, -44, 7, -62, 78, 97, 25, 104, -24, 13,
  102, -105, -151, -105, -20, -15, -26, 71, 76, 12, 4, 47, -19, 27, -126,
  -120, 77, 40, 41, 76, 108, 62, -110, 22, 52, -87, 80, -29, 24, -37, 90,
  -141, 192, 87, -96, -133, -2, 5, 24, -7, 66, 71, -68, 18, 37, -29, 45,
  -12, 96, 182, 48, 16, -30, -132, 91, 57, 7, 51, -43, 32, 79, 23, -116,
  -14, -26, -36, -3, -90, -49, -2, 21, 115, 10, 38, -10, 87, 11, -40, 97,
  -4, 116, 79, 38, -22, -48, -69, 31, 186, 151, 50, 59, -28, 134, 64, -68,
  -1, 1, 34, 117, 58, 0, 62, -5, -103, 27, -81, -61, 28, 38, 135, 44, 24,
  14, 190, 73, -5, 63, 50, -1, 104, 2, 20, 72, -35, 51, -33, 134, -24, -17,
  -46, -3, -175, 68, -15, -115, 3]

theorem fractionalNearFrameSubtreeG2R0272_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0272Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0272Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0272Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0272_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0272LowerBoundTable : List ℤ :=
  [36, 298, 169, 219, -28, 56, 1, 2, 3, 426, 331, 11, 342, 240, 172, -107,
  416, 93, 11, 76, -118, -241, 71, -184, 175]

def fractionalNearFrameSubtreeG2R0272LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0272Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0272LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
