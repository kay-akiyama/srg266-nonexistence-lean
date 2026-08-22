import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0496`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0496Mask : ℕ := 5811316919293460

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0496Witness : Array ℤ :=
  #[1085, 1092, -25, 338, 995, 566, -969, 70, 158, -638, 5, 0, 92, -1072,
  -295, -850, 35, -17, 316, 656, -350, 514, -874, -613, -777, -755, 1298,
  613, 1190, 874, 1204, 1580, 1015, 296, 613, 333, -1391, -1615, 825, 703,
  500, -429, -627, -377, 1029, 715, -176, -1307, 57, -412, 657, 523, 656,
  -488, 812, -1007, 633, 1254, -449, -209, 617, 1276, 164, 954, 736, 101,
  51, 516, -851, -36, 51, 362, 623, 1021, 714, 729, 792, -227, -320, -682,
  -299, -1025, -208, -610, -335, 432, 330, -458, 169, 321, 748, -68, 289,
  278, 226, 698, 19, -15, -262, 872, 487, 154, 272, -297, 11, 1254, 214,
  -488, -1212, -117, -107, 35, -296, -1233, 215, -1164, -742, -340, -203,
  512, 1004, 1558, 571, 307, 175, 643, -146, -5, 51, 591, 486, 422, 930,
  228, 168, 802, -755, -1200, 128, -786, -897, 608, 309, 187, 470, 208, 319,
  -649, 896, -49, -694, -518, -1457, -1710, -732, 662, -873, -471, -421,
  -1016, -625, -39, -1264, -717, 526, -325, -512, -299]

theorem fractionalNearFrameSubtreeG2R0496_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0496Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0496Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0496Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0496_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0496LowerBoundTable : List ℤ :=
  [-256, -1896, 32, 531, 32, 2323, 2067, 6, 1463, 3254, -517, 2362, -2494,
  -598, 3208, -104, 2417, 101, 536, 101, 1972, -1206, 1257, 4210, 100]

def fractionalNearFrameSubtreeG2R0496LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0496Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0496LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
