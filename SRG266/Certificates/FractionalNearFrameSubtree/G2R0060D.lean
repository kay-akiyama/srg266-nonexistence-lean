import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0060`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0060Mask : ℕ := 953992538194506

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0060Witness : Array ℤ :=
  #[-21, 3, 10, -57, 146, 118, -287, 87, -327, -323, -129, 432, 271, 98,
  124, 254, 123, 128, 155, 26, -90, 178, 111, -104, 15, -3, 26, 128, -72,
  -182, -29, 34, -74, 276, 297, -108, 339, -32, 14, 224, 203, 162, -409,
  -215, -212, -26, -138, -289, 99, 100, 131, 340, 158, 86, -2, 144, 288,
  -66, 110, -114, 296, 97, -84, 597, -101, -114, -53, 51, 54, 126, -40, 84,
  -44, 94, 262, 371, -109, -46, 395, 171, -90, -71, 266, 14, 91, 250, 143,
  -25, 1, 82, 162, 135, -97, -42, -355, 441, 88, 142, 235, -204, -127, 94,
  31, 157, -170, 28, 50, 83, 230, -229, 79, 76, -24, 243, 115, -45, -174,
  19, 225, -48, 0, -20, 81, 176, 48, -17, 19, 57, -30, -239, 156, 101, 40,
  111, 141, -149, 143, 28, 133, 400, 115, 394, -19, -53, 341, -13, -69, 121,
  77, 126, 16, -206, -214, 33, -44, -87, 204, 4, 12, 91, -207, 94, -4, 418,
  40, 139, -35, -14]

theorem fractionalNearFrameSubtreeG2R0060_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0060Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0060Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0060Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0060_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0060LowerBoundTable : List ℤ :=
  [478, 581, 1, 308, 906, 384, 762, 553, 494, 34, 1057, 323, 225, 950, 1317,
  10, 334, 755, -402, 394, 579, 1689, 1604, 1598, 1408]

def fractionalNearFrameSubtreeG2R0060LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0060Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0060LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
