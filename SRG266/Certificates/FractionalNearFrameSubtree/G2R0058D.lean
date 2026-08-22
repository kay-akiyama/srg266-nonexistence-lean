import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0058`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0058Mask : ℕ := 948367051563240

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0058Witness : Array ℤ :=
  #[-516, 667, -996, 502, -587, -670, 477, -72, 801, 250, -586, 162, -242,
  -103, -696, -504, -1096, -376, -730, -663, 380, -158, -635, -400, 1492,
  1292, 822, 1089, -355, -453, -221, -253, -525, 257, 974, 353, 293, 0, 27,
  655, 1333, -228, -506, 272, 380, 21, 431, -142, -214, 10, 794, 553, 2,
  -720, -356, 12, 871, -1829, 240, 980, -578, 457, 1384, -28, -823, 1025,
  1839, -274, -239, 1053, 1036, 599, 384, -367, -390, 515, -579, -327, -523,
  -395, -48, 333, 1159, 502, 901, 14, -264, 687, 223, 688, -109, 108, -396,
  -242, 1012, -1283, 553, -921, 1460, -663, 763, -360, 455, 1045, 234, -88,
  -238, -146, 179, 261, 400, 383, 454, 797, 161, 682, 376, 1319, 453, 474,
  328, -924, 1267, 835, -1253, -25, 339, -257, -1023, 294, 323, 323, 330,
  40, 277, 665, -188, 1075, 695, -1247, 1748, -205, -123, 1273, 111, -331,
  1128, -905, -474, -442, 296, 147, 524, 509, 124, -1166, -870, -628, 1298,
  929, -437, 697, 32, -108, -945, -297, 576, 0]

theorem fractionalNearFrameSubtreeG2R0058_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0058Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0058Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0058Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0058_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0058LowerBoundTable : List ℤ :=
  [1095, 1559, 2332, 1968, 1473, 32, 1341, 32, 1219, 2114, 2511, 398, 4375,
  2181, 4762, 20, 3055, 1045, 2063, 339, 4451, 99, 3684, 1148, 104]

def fractionalNearFrameSubtreeG2R0058LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0058Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0058LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
