import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0367`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0367Mask : ℕ := 5715934420579852

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0367Witness : Array ℤ :=
  #[-64, -17, -207, -830, -1159, 505, 192, 162, 204, -180, 150, 633, 0, 480,
  309, 228, 598, 341, 0, 588, -385, 37, 239, -69, -478, 143, -84, -10, -164,
  -122, 547, 634, -499, 408, 214, 460, 686, 59, -679, -635, -751, 287, 279,
  13, 591, 386, 496, -456, 83, -222, -115, -155, 918, -61, 430, -460, 856,
  -101, 307, 543, -750, 502, 686, -670, -686, -80, 280, 181, 115, 550, -455,
  814, -265, 408, 642, -88, -73, -411, -158, 28, -500, 0, -220, 35, 587,
  121, 61, 194, -491, 669, -259, -30, 453, -591, -187, 200, -496, -185,
  -427, 401, 311, 273, 353, 243, 896, 458, 730, -308, -362, 107, 461, -451,
  -128, -270, -15, 195, 8, -249, 765, -618, 300, 252, -584, 186, -263, 270,
  -294, 339, -335, 158, -484, -53, 89, -298, -61, 826, -49, 512, -370, 36,
  653, 311, 184, 325, -28, 376, 519, 516, 279, -189, 29, -393, 357, 297,
  221, 171, -568, 527, -144, -428, -425, 297, 310, 420, 578, 408, -264, 471]

theorem fractionalNearFrameSubtreeG2R0367_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0367Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0367Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0367Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0367_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0367LowerBoundTable : List ℤ :=
  [348, 1245, 694, 31, 1116, 858, 33, 1459, 1115, 102, 893, 1082, 476, 4803,
  2222, 2025, 1773, 735, -4, 1577, -874, 1003, 1220, 136, 1881]

def fractionalNearFrameSubtreeG2R0367LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0367Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0367LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
