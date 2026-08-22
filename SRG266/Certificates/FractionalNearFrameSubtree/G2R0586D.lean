import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0586`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0586Mask : ℕ := 6850825775977072

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0586Witness : Array ℤ :=
  #[131, -34, 283, 279, -262, 378, 559, 163, -98, -111, -70, 170, -23, 215,
  506, 177, -335, 471, -123, 695, 1015, -93, 22, -17, 491, 62, -34, 168,
  484, -10, 495, 691, -1412, -494, 0, 499, 584, -381, -380, 523, 426, 638,
  130, 350, 451, 13, -243, -16, -277, -62, 426, 286, 173, -588, -44, -150,
  -184, 171, -124, -138, 592, 309, 309, 933, -385, 908, 298, -157, -587,
  -25, 201, -17, -77, 337, -768, 736, 319, 265, -223, -307, 384, 376, -142,
  682, -295, -127, -84, 140, 100, -208, -10, 132, -154, -32, 449, 481, -498,
  -550, 559, 466, -70, 591, -199, 70, 78, 441, 852, -720, -67, 212, 306,
  336, 495, 849, 507, -406, 95, -70, 76, -430, -362, 336, 471, 673, 160, 66,
  -62, 184, 178, 255, 481, -2, 262, 67, 256, 13, 331, 182, 219, -109, 97,
  171, -163, -110, -217, 347, 236, 4, 32, -788, -163, -375, -130, 104, -285,
  -201, -346, 16, 142, -115, 121, 188, -266, 159, 0, -595, -160, -651]

theorem fractionalNearFrameSubtreeG2R0586_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0586Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0586Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0586Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0586_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0586LowerBoundTable : List ℤ :=
  [832, 152, 584, 40, 931, 1738, 1221, 1908, 820, 593, 1590, 1500, 982,
  -550, 623, 1874, 1018, 254, 9, -104, 1633, 2571, 1597, 1204, 3799]

def fractionalNearFrameSubtreeG2R0586LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0586Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0586LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
