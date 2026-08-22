import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0071`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0071Mask : ℕ := 866326412904969

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0071Witness : Array ℤ :=
  #[311, -197, 681, 523, 0, -149, 1147, 650, 816, 709, 1053, 178, -297,
  -396, -1206, 0, -627, -1494, -13, 592, -64, -400, -520, -408, 571, -222,
  -366, -686, 622, 1292, 563, 983, 430, 438, 354, 363, 117, -482, -1024,
  -237, 271, 569, 890, -90, 0, -232, 20, -10, 217, 321, -376, -738, -138,
  -249, 563, -283, 81, 326, -991, 508, 210, 397, -222, -437, -24, -440,
  -148, 128, 176, 200, -477, -829, 607, -129, 574, -586, 136, -15, 358, 226,
  -101, -284, 663, 50, -573, 138, 33, -731, 392, 257, 288, -99, -734, -122,
  590, -159, -77, 45, -34, 354, -658, 156, 305, -27, 289, -33, 103, 271,
  229, 53, 989, 558, 601, 325, 639, -284, -62, 108, 302, -210, -108, -1029,
  -145, -345, -856, -202, 606, -31, -125, 134, -545, 259, 220, 900, 602, 25,
  0, 306, -733, 78, 568, 498, -197, 619, -532, 1006, 757, 456, 380, 352,
  -348, 388, -33, 89, 813, -289, 379, -141, 297, -7, -352, 206, -452, 382,
  -18, -22, 938, -842]

theorem fractionalNearFrameSubtreeG1R0071_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0071Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0071Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0071Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0071_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0071LowerBoundTable : List ℤ :=
  [302, 1523, 500, -330, 1128, 168, 1365, 482, 1660, 2882, 1831, 2227, 99,
  671, 2150, -1016, 100, 583, 1740, 1850, 553, 296, 1298, 1071, 100]

def fractionalNearFrameSubtreeG1R0071LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0071Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0071LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
