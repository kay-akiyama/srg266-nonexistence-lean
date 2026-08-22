import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0185`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0185Mask : ℕ := 6866166870680354

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0185Witness : Array ℤ :=
  #[-44, -372, 51, 271, -35, 102, 98, 357, 0, 602, 163, -380, -220, -267,
  -275, -12, -76, -311, 447, -112, 486, -347, -112, 135, 354, -298, 193,
  -98, -16, 103, 376, 376, 228, 114, -68, -274, -128, -353, 352, -7, 4, 259,
  -52, -700, -153, -335, -176, 297, 383, 267, -243, -90, -272, -90, 345,
  156, 40, 121, 218, -303, -309, 243, -29, -66, -389, -211, 152, -477, -258,
  -407, -215, 252, -146, -41, -94, 369, 315, -68, 186, -135, 11, 282, -98,
  5, -245, -259, -148, -380, -203, -230, 320, 91, 58, 409, 229, -15, -126,
  -22, 268, 131, 230, -83, 357, 330, 18, -29, 284, -105, -696, 272, -366,
  -141, 55, 149, 11, 514, 51, 571, -67, 7, 278, 82, -192, -491, -120, 321,
  374, -301, -75, -11, -383, -120, 431, -563, 637, 314, -188, 373, -56,
  -847, 500, 154, 57, 370, 123, 99, 152, 250, 210, 243, -454, -264, 138,
  111, 76, -161, 767, -77, 277, 13, -316, 362, 522, -139, 728, 70, -183,
  157]

theorem fractionalNearFrameSubtreeG3R0185_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0185Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0185Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0185Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0185_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0185LowerBoundTable : List ℤ :=
  [-181, 1071, 23, 0, 1, 587, -99, 563, -166, 1264, -90, 1911, 1101, -240,
  -504, 2009, -398, -79, 1608, 1098, -107, -136, 8, -518, 9]

def fractionalNearFrameSubtreeG3R0185LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0185Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0185LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
