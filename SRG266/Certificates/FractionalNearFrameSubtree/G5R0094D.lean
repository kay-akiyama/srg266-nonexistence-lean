import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0094`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0094Mask : ℕ := 5511492379708194

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0094Witness : Array ℤ :=
  #[-270, 239, 108, 368, -78, -138, 685, 340, 179, -9, 548, -369, 0, -721,
  -133, -166, 391, 672, 796, 39, 243, 169, 195, -39, -152, -154, -495, -502,
  -10, -907, 604, -990, -750, 231, 0, 703, 833, 595, 29, 694, -645, 28,
  1092, 108, 182, 185, -259, 487, 485, -676, -672, -168, -484, 954, 0, 14,
  642, 0, -154, -489, -237, -604, -256, 1059, 333, -705, -496, 56, 347, -81,
  14, 388, -115, -653, 640, -103, 32, 1058, -351, 186, -200, 186, 298, 1248,
  405, 90, 85, 56, -400, -61, -275, -485, -22, -424, 200, 205, -44, -274,
  1036, 170, 278, 290, 188, -181, -386, 268, 61, -37, -62, -170, -128, 285,
  209, 435, -547, -559, -211, -295, 325, 0, 472, 453, -237, -343, 153, -284,
  788, 793, 171, -50, -155, -95, 307, -273, -297, -12, 776, 124, -205, -453,
  -318, 471, -7, 19, 0, -1022, -208, -270, -504, -832, -169, 394, -740, 329,
  -264, 0, -315, 221, 509, 937, 330, 579, 81, -176, -404, 229, -53, 509]

theorem fractionalNearFrameSubtreeG5R0094_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0094Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0094Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0094Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0094_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0094LowerBoundTable : List ℤ :=
  [-51, -259, 721, -194, 1011, -7, 1254, 106, 551, 508, 438, -903, 1453,
  -135, 101, 1775, 1458, -147, 350, 1198, 2503, 1610, 367, -269, 2152]

def fractionalNearFrameSubtreeG5R0094LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0094Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0094LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
