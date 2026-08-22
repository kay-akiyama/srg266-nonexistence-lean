import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0096`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0096Mask : ℕ := 945962027172428

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0096Witness : Array ℤ :=
  #[41, -103, 90, -131, -90, 75, 18, 92, 93, -37, 37, 42, 77, 49, 11, 1, 81,
  -51, -40, 0, 9, 84, -35, 18, -119, -38, 48, 68, 44, 91, -75, -91, 0, -50,
  42, 12, -52, 75, -49, -4, 22, -64, 41, 34, 8, 1, -97, 47, 7, -1, 55, -93,
  -8, 0, 98, 127, 62, 67, -5, -89, 10, 13, -65, -10, -47, -8, -56, -46, 56,
  62, -123, -67, 56, -13, -85, 134, -98, -56, 18, 33, 0, 61, -12, 30, 78,
  -22, 71, 46, 110, 143, -1, -88, 70, 14, 74, 41, 171, 19, 84, 39, 1, 36, 3,
  1, 110, -14, 26, 21, -27, -14, -42, -11, -32, -7, -21, 3, 17, -64, -111,
  103, 15, -175, -109, 98, -20, 8, 42, 15, -53, 69, -60, -34, 30, -11, 115,
  41, 35, -135, 18, 40, -17, 11, -5, 14, -20, -64, 17, 11, 19, 3, -30, 103,
  -10, 61, 66, 40, -123, -82, -16, 2, 79, 110, 14, -48, 27, -27, 64, -23]

theorem fractionalNearFrameSubtreeG1R0096_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0096Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0096Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0096Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0096_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0096LowerBoundTable : List ℤ :=
  [-3, 41, 114, 231, -54, 162, 49, 137, -42, 199, -69, 50, -125, -28, 70,
  11, 119, 398, 489, 380, 423, 9, 17, -210, 73]

def fractionalNearFrameSubtreeG1R0096LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0096Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0096LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
