import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0635`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0635Mask : ℕ := 11341284909487378

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0635Witness : Array ℤ :=
  #[52, -14, 35, 32, -16, 170, 487, 522, 324, 335, 497, -263, -357, -287,
  -62, -592, 9, -112, 189, 26, -349, -212, 145, 166, -93, 92, 63, -102, 280,
  124, 77, 0, 75, -231, -123, 5, 37, -161, 123, -159, -64, 272, 7, 191, 179,
  257, -14, 41, 10, 12, 254, -198, 21, 1, 108, -50, 248, 33, 186, 13, -125,
  -380, 208, 346, 9, -135, -529, -249, -55, 225, 48, -232, -86, -160, 419,
  239, 248, 22, -96, 312, 363, 302, 198, -22, -183, 470, 157, 166, -85,
  -127, 659, 117, 135, 232, 232, -38, -117, -121, 55, 272, -12, 95, -176, 6,
  -45, 43, 300, -120, 169, -486, 230, -325, 249, 253, -24, 185, 45, -46,
  -385, 79, -331, 613, 15, 49, -190, 103, 63, -26, -149, 294, 437, 183, 177,
  88, 99, 41, 192, -50, 270, 247, 171, 469, -150, 201, -46, -5, 83, 316, -6,
  -83, -80, 428, -233, -161, 228, 434, 142, -129, -104, 231, 293, 273, 36,
  44, 110, 60, -251, 314]

theorem fractionalNearFrameSubtreeG2R0635_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0635Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0635Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0635Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0635_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0635LowerBoundTable : List ℤ :=
  [448, 1223, 745, 359, 248, 269, 651, 1371, 647, 254, 1851, 1250, 666, 542,
  1533, 1486, 2078, -347, 399, 568, 1020, 74, 11, -84, 59]

def fractionalNearFrameSubtreeG2R0635LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0635Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0635LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
