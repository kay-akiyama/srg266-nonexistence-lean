import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0114`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0114Mask : ℕ := 5793786952789001

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0114Witness : Array ℤ :=
  #[181, 46, -1083, 98, 179, -75, -567, 0, -567, -551, -104, 524, 1370, 265,
  1357, 196, 350, 1977, 1651, 722, 452, -8, 304, 843, 443, -213, 522, -1227,
  -2056, -1416, -1570, -96, -348, 259, 46, 757, 64, -346, 39, -491, -656,
  1050, 147, 987, 680, 1206, -1014, 394, 249, -377, 186, -723, -519, -792,
  974, 557, 452, 1240, 367, -765, -84, 516, 0, 188, 1188, 711, -346, -1777,
  228, -1194, 638, 1105, 308, 226, 515, 619, 229, -710, 256, 29, -467, -311,
  266, 162, -464, -580, -912, -406, -1154, 286, -61, 518, 36, 764, 74, -31,
  176, 1596, 0, 1813, 90, 265, 306, 274, 484, 349, -51, -679, -335, 476,
  302, 1625, 1251, 926, -509, -173, 966, -666, -339, -1068, 1800, 1417,
  -422, -1696, -638, -1673, -170, 130, 332, 343, -636, -6, 123, -155, 232,
  -358, 122, 257, 301, -494, -784, 20, -661, -364, 318, -722, 1055, 244,
  -987, 290, 40, -790, 1058, -36, -287, 625, 357, 404, -236, 720, -81, -278,
  -683, 693, -671, 1339, 138, -403]

theorem fractionalNearFrameSubtreeG5R0114_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0114Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0114Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0114Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0114_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0114LowerBoundTable : List ℤ :=
  [-107, 177, 3335, 1251, -1264, 1868, 32, 32, 164, -494, 1938, -831, 100,
  2155, 5364, 5579, 3798, -3316, 99, 6361, 1066, -2264, 2223, 632, 100]

def fractionalNearFrameSubtreeG5R0114LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0114Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0114LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
