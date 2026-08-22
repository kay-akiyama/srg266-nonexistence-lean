import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0158`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0158Mask : ℕ := 1379489567047906

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0158Witness : Array ℤ :=
  #[303, 107, 231, -39, -273, 67, -243, 0, -197, 204, -43, 34, -149, -45,
  140, 96, -46, -2, 114, 31, 71, -77, 4, -70, 49, 31, 43, -37, -94, -101,
  -50, 55, -212, -480, -314, -22, 119, 57, 143, 255, 0, 87, 148, 202, 7,
  -58, -240, -266, 163, 144, -173, 160, 135, -153, 133, -56, 77, -185, 340,
  -30, 153, 261, -37, -69, 80, -36, -255, 52, 233, -46, -152, 66, -201,
  -211, -51, 253, 46, 148, 247, 27, -38, 89, 62, -203, 121, 379, 19, 288,
  40, 286, 382, -22, 87, 163, 257, 133, 293, 98, -84, 314, 10, -46, -155,
  -220, 204, -235, -225, -147, 80, 43, 137, 211, 211, -41, -8, 43, 136,
  -168, 84, -41, -360, 64, 136, -265, -72, 12, -83, -76, 105, -95, 232, -64,
  -142, -87, 159, 225, 285, 17, -87, 193, -51, 124, -224, -170, -192, 65,
  170, 137, -17, -157, 168, -45, -372, 40, -88, 137, 87, -81, 142, 91, 233,
  -10, 83, 167, 9, -369, 37, 145]

theorem fractionalNearFrameSubtreeG2R0158_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0158Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0158Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0158Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0158_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0158LowerBoundTable : List ℤ :=
  [-43, 3, 2, 583, 333, 205, 162, 399, 393, 210, 228, 212, -186, 195, -223,
  -185, 116, 581, 1089, 503, 530, 9, 671, 238, 9]

def fractionalNearFrameSubtreeG2R0158LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0158Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0158LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
