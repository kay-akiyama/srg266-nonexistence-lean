import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0101`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0101Mask : ℕ := 5542726887711060

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0101Witness : Array ℤ :=
  #[-167, 382, -208, -132, -651, 309, 565, -81, -432, -417, 284, -164, 633,
  -185, -631, 512, 357, 56, 452, -167, 42, -102, -548, -564, 0, -119, -76,
  -14, 581, -27, -151, -356, 136, -378, 441, 535, 333, 0, 164, 238, 464,
  -122, -412, -525, 10, 235, -550, 218, -376, 252, 523, 653, -256, -340,
  -218, 320, 41, -24, 349, 168, -296, 302, 63, 78, 196, -124, 174, -159,
  -420, 200, 294, 191, -340, 454, -150, -297, 303, -66, -690, 294, -29, 32,
  941, -687, -399, 341, 1063, 87, -77, 267, -300, -4, 350, 239, 24, 212,
  -283, 29, 603, -80, -456, 626, 467, 917, 681, -392, 358, 75, 139, 366, 45,
  -93, -411, 0, 615, 25, 105, -96, 25, -60, 185, -375, -355, -602, 380, 493,
  459, -645, 711, 115, 692, 320, -55, 117, -300, 199, 264, 278, 107, 84,
  -247, 60, 45, 178, 19, 578, 67, -445, 106, 25, 157, 179, 512, -217, -378,
  -29, 37, -91, -663, 242, 514, -90, 103, 563, 433, -562, 115, 80]

theorem fractionalNearFrameSubtreeG5R0101_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0101Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0101Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0101Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0101_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0101LowerBoundTable : List ℤ :=
  [510, 557, 459, 661, 32, 1057, 243, 570, 604, 3090, 646, 1830, 178, 2150,
  1360, 399, 250, 991, -774, 511, -610, 3764, 938, 1632, 610]

def fractionalNearFrameSubtreeG5R0101LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0101Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0101LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
