import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0612`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0612Mask : ℕ := 9578862305725449

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0612Witness : Array ℤ :=
  #[279, 517, 378, 183, 161, -5, 0, -139, 136, 56, -417, -452, 87, -48,
  -163, 0, -206, -136, -583, 309, 288, 59, -294, -476, 448, 293, 54, -301,
  84, 96, 433, 183, 22, 246, 212, 515, -589, -191, -421, -182, 215, 276,
  250, 220, 501, 17, -72, 331, -134, 203, -204, -101, -60, -118, -51, -164,
  -15, 116, -58, -143, 296, 34, 265, -460, -217, 39, 217, -399, 642, -372,
  -81, 108, -450, 375, 6, 11, -46, -2, -450, -377, 108, 24, -20, -45, 30,
  -192, 587, -723, -5, -631, -406, -572, 380, 218, 423, 335, 139, -322, -55,
  -110, -479, 359, 173, 464, 183, 385, 23, 429, 328, 467, 321, 366, 393,
  238, 392, 150, 90, 89, -379, -328, -42, -138, -145, 127, -34, 138, -244,
  -42, 201, 219, -130, -379, 79, -156, -93, 89, 307, -124, 202, -355, 178,
  186, -450, 878, 391, 366, 267, 374, 322, 300, 476, 416, 413, 166, 249,
  -337, -240, -350, -262, -272, -417, -423, 217, -328, -226, -77, 209,
  -1017]

theorem fractionalNearFrameSubtreeG2R0612_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0612Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0612Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0612Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0612_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0612LowerBoundTable : List ℤ :=
  [-63, 343, 31, 32, -156, 33, 25, 68, 32, 3168, 594, 425, 134, 3079, 56,
  99, 222, 976, 1325, 774, 334, 334, 455, 1173, 77]

def fractionalNearFrameSubtreeG2R0612LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0612Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0612LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
