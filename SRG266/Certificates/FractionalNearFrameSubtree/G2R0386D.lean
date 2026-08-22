import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0386`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0386Mask : ℕ := 5739217303776408

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0386Witness : Array ℤ :=
  #[413, 212, 459, 387, 541, 229, -375, -374, -563, -332, 169, -418, -500,
  -373, 90, -51, 114, -85, -288, -85, 353, -51, -114, 221, -39, 297, 276,
  103, -683, 14, 131, -195, 265, 396, 321, -605, -345, -435, 271, 284, 263,
  -72, 13, -183, -306, -338, 416, 2, -286, -133, 108, -64, -344, 558, 137,
  67, 407, -241, 223, -631, 219, -254, -404, 362, -98, 242, 362, 356, 235,
  425, -356, 438, 150, -479, 330, -82, 638, -5, 350, -135, 495, 469, -441,
  -190, -69, 91, -427, -187, 141, 242, 151, -340, 22, 427, 450, -121, 153,
  112, 247, -600, -12, -270, -39, -192, -39, 13, 50, 220, -37, -318, -532,
  -268, 85, -90, -121, 28, 110, 48, 359, -374, -155, 260, -208, 306, -523,
  -202, -874, -392, -229, -480, -100, 138, -2, 82, -46, 281, 262, -322, 445,
  104, 387, -178, 188, 47, -456, 74, 294, -100, 64, -11, 322, -74, -122,
  108, -19, 88, 109, 256, 220, -207, 267, 78, -311, -353, -171, 144, 45, 51]

theorem fractionalNearFrameSubtreeG2R0386_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0386Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0386Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0386Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0386_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0386LowerBoundTable : List ℤ :=
  [-439, -500, 295, 828, -266, 32, -137, -493, 32, -424, 1035, -929, 356,
  416, -94, 85, 101, 225, 1058, -14, -574, 1350, 1160, 101, 205]

def fractionalNearFrameSubtreeG2R0386LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0386Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0386LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
