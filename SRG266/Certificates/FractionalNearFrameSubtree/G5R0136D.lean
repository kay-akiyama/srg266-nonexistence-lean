import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0136`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0136Mask : ℕ := 6074167454960930

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0136Witness : Array ℤ :=
  #[220, 319, -165, 326, -138, 157, 462, 289, -288, 56, -41, 189, 69, 276,
  -525, -60, 134, -389, 25, -47, -5, 96, 204, 359, 98, 98, -495, 131, 164,
  159, -366, -116, 104, 80, 314, -191, -310, 557, 54, 448, 0, -96, 148, 233,
  -41, 65, 330, 259, -113, -354, -260, 33, -8, -79, -237, -366, -332, 319,
  -26, 604, 340, 426, 416, -98, 140, 264, -37, -56, 257, 194, 427, 199, 309,
  231, -103, -53, 231, 142, 0, 91, 879, -266, 407, 78, -183, -318, 682, 251,
  256, -37, 411, 162, 367, -79, -66, 42, -202, -412, 155, 176, 489, 410,
  326, 9, -162, -86, 440, -11, 528, -585, 43, 298, 0, 445, -128, 742, 0,
  -869, -51, -242, 249, 283, -382, 362, -193, 124, -14, 103, 140, 112, -217,
  246, -16, 218, -260, 501, 114, 244, 744, -112, 182, -608, -16, 246, -30,
  -491, 21, 202, 488, 235, 0, 385, -19, -350, -85, 493, -171, -460, -409,
  -52, 234, -382, 284, 131, -25, 420, 745, 390]

theorem fractionalNearFrameSubtreeG5R0136_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0136Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0136Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0136Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0136_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0136LowerBoundTable : List ℤ :=
  [705, 1049, 976, 1645, 749, 850, 832, 654, 582, -121, 1216, 280, 394,
  2424, 402, 1166, 1301, 571, 1341, 2, 996, 1207, 248, 792, 3335]

def fractionalNearFrameSubtreeG5R0136LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0136Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0136LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
