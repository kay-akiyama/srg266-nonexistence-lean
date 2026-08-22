import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0191`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0191Mask : ℕ := 6866918487968920

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0191Witness : Array ℤ :=
  #[239, 380, 508, -352, -149, 158, 21, -73, 0, -223, -463, 642, 246, 964,
  -18, 33, 83, -940, -29, 595, 1051, 293, 504, 303, -894, 260, 0, -129,
  -550, 305, 136, 1099, 571, 126, 484, 767, 361, -257, 297, -755, -49, -495,
  593, 225, 679, -1187, -193, -136, 738, 984, 514, -583, 279, 107, 940, 388,
  -168, 1615, -279, -106, -707, -191, -382, -817, 221, 612, 338, 54, -581,
  278, -48, 1707, 823, -261, -17, 457, -111, -28, 982, 1490, 630, -527,
  -337, 187, 253, 555, 429, -403, 205, 566, 547, -1424, -887, 320, 1364,
  -787, 1064, -310, 83, -275, 348, 540, 351, -18, 663, -151, 936, 80, -388,
  -194, 542, 101, -870, -75, -264, 1124, 23, 414, -146, -698, 374, 543, 258,
  -237, -860, -705, 851, 969, -283, -892, -280, -218, -611, -83, 170, 1565,
  -71, 729, -806, -727, 1231, -969, 552, -359, 434, -294, 326, 394, -660,
  1085, -445, -376, 649, 1222, -279, 1107, -488, 963, 2044, 202, -528, 231,
  528, -487, -530, 1246, 213, 1085]

theorem fractionalNearFrameSubtreeG3R0191_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0191Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0191Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0191Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0191_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0191LowerBoundTable : List ℤ :=
  [1239, 1124, 2859, 1749, 1787, 393, 580, 1423, 1760, -670, 2724, 2440,
  4651, 2759, 326, 4816, -1416, 4546, 1313, 2012, 2299, 3187, 2140, 615,
  5975]

def fractionalNearFrameSubtreeG3R0191LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0191Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0191LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
