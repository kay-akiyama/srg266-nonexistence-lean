import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0218`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0218Mask : ℕ := 2378894743687713

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0218Witness : Array ℤ :=
  #[0, 525, -289, 125, 507, -55, -623, -162, -490, 413, -1121, 16, 900,
  1099, 272, 668, 0, 1267, 431, 323, 88, -125, 168, 848, 622, 624, 148,
  -175, 334, -258, -727, 97, 99, 80, 29, -249, -421, 375, 1095, -53, 336,
  -439, 483, -880, 950, -5, 189, -214, -202, 308, 72, 482, -43, 385, 435,
  80, -250, -395, 287, 1126, -1, -102, -1118, 94, 112, 330, -136, -322, 326,
  -93, 735, 342, -160, -241, 185, 425, 58, 485, 107, -284, -165, 25, -40,
  63, 299, -578, 136, -309, 113, -295, -89, 568, -382, -322, -233, -547,
  -33, 365, -243, 257, 24, 109, -17, 675, 519, -124, 1010, -163, 948, -481,
  -177, -604, 757, 92, -535, 16, 949, 487, 473, 262, 368, 65, 357, 456, -27,
  10, -148, 146, -77, 230, -762, -465, 142, -639, 816, 292, -120, -535, 51,
  119, -422, -1464, 144, -1227, 390, -86, 468, 204, 631, 826, 139, 135,
  -572, 486, 0, -101, 159, -745, -71, -590, -153, 97, -612, 338, -319, 424,
  422, -758]

theorem fractionalNearFrameSubtreeG2R0218_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0218Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0218Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0218Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0218_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0218LowerBoundTable : List ℤ :=
  [455, -137, 41, 710, 626, 1354, 763, 2218, 463, 1669, -2094, 1765, 319,
  496, -797, 1518, 1954, 1076, 1861, 1173, 100, 261, 100, 3001, 2728]

def fractionalNearFrameSubtreeG2R0218LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0218Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0218LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
