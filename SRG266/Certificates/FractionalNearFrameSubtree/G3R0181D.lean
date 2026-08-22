import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0181`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0181Mask : ℕ := 6865892387034642

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0181Witness : Array ℤ :=
  #[352, 150, 62, 279, -239, -38, 856, 22, 387, 305, 109, -137, -559, -519,
  -366, -370, -156, -316, -189, -188, -463, 385, -310, 81, 177, -211, 380,
  305, -129, 17, 210, 479, -405, 441, -466, -516, -76, -37, -227, -71, 355,
  -8, 497, 140, 15, 224, 304, 239, -101, -339, 76, 370, 244, 877, 153, 157,
  -503, 51, 359, 384, -86, -267, 351, -94, 564, -160, -337, 434, -44, -224,
  167, -89, 374, -51, -328, -325, -102, 58, -278, 33, -120, -275, 166, 464,
  -315, -132, 213, 144, 541, 443, 187, 60, 440, 154, 87, 312, 268, -251,
  384, 121, 382, 727, -183, 598, 213, 617, 591, 542, 560, -234, -8, -213,
  -249, -270, -192, -97, -191, 311, -104, 965, -3, 390, 304, -75, 77, -69,
  269, -113, -361, 200, -391, 430, 113, 41, -354, -202, -210, -88, -207,
  -72, 247, -115, -96, 323, 261, 135, 321, 175, 33, -5, -83, -318, -247,
  -221, -67, 642, 151, 288, 110, 385, -293, -67, 218, -495, 157, 719, -66,
  -217]

theorem fractionalNearFrameSubtreeG3R0181_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0181Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0181Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0181Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0181_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0181LowerBoundTable : List ℤ :=
  [237, 615, 1204, 118, 906, 650, 1, 1535, 1, 484, 10, 2192, -467, 3919,
  1342, 1179, 833, 382, 1080, 1071, 425, 381, 432, 548, 1524]

def fractionalNearFrameSubtreeG3R0181LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0181Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0181LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
