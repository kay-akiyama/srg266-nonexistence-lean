import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0230`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0230Mask : ℕ := 2901151273681234

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0230Witness : Array ℤ :=
  #[68, -139, 66, 3, -96, -124, 270, 61, 174, 216, 233, -63, -146, -92,
  -246, -138, 26, 381, 51, -12, -114, -263, -81, -48, 29, -83, 181, 22, 99,
  -47, -59, 84, 196, -70, 53, -164, -80, 275, 170, -196, -236, -235, 79, 0,
  267, 81, 368, 303, 361, 301, -372, -326, 0, 33, 62, 239, 96, -481, -277,
  64, -184, -66, -10, -41, 269, 233, 244, 187, 76, -116, 31, -25, 22, -209,
  104, 119, 110, 76, 10, -159, -326, -186, 25, 212, -69, 163, 43, 225, -77,
  36, -63, 191, 150, 265, 69, 267, 58, -154, -26, 36, 91, -201, 14, 26, -5,
  100, 117, 222, -3, 263, 226, 72, -127, -45, -207, -162, 104, -4, -262, 17,
  -47, 289, 0, 107, 144, 156, 29, 34, 69, -43, -85, 25, -80, -107, 160, 245,
  160, 21, 43, 9, 17, -164, 178, 44, 274, 110, 140, -74, 309, 109, 332,
  -136, -47, -237, 128, -265, -38, 159, -32, 21, 7, -18, 104, 285, -34, -53,
  -143, 190]

theorem fractionalNearFrameSubtreeG2R0230_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0230Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0230Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0230Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0230_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0230LowerBoundTable : List ℤ :=
  [177, 489, 567, 158, 621, 482, -166, 275, 221, 493, -184, 581, 712, 1450,
  364, 801, -220, -57, 128, 11, 327, -338, 1693, -197, 477]

def fractionalNearFrameSubtreeG2R0230LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0230Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0230LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
