import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G4R0032`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0032Mask : ℕ := 5424769746668806

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0032Witness : Array ℤ :=
  #[-101, -210, -156, -991, 158, 1, -370, -396, 672, 334, -254, -137, -46,
  -277, 1479, -426, -681, -1137, -939, -588, -698, 706, -107, -139, 1077,
  -258, -60, 0, 292, 1215, 529, 449, 437, 427, 176, 257, 973, -276, -222,
  455, -782, -98, 492, -474, 42, -182, -103, 586, 223, 377, 898, 614, 440,
  -507, 316, -382, 49, 256, -242, -104, -562, 85, 367, -12, 270, 64, 199, 6,
  355, 22, 167, 263, 88, -108, 667, -517, 0, -2, -103, 231, 440, 8, -46,
  546, 286, -29, 280, 175, 453, -395, 42, 31, -756, 710, -211, -201, 179,
  969, 308, -249, -845, 398, 535, -221, 639, -474, -449, -485, 285, 106,
  -242, 987, -727, 158, -624, 122, -171, 1019, -188, -102, 300, -53, -157,
  -422, 0, 1030, 71, -800, -121, -131, -349, 1108, -801, -1191, -683, 738,
  -623, -138, 127, -282, 202, 526, -254, 554, -220, -360, 513, -18, 151,
  316, 712, -573, -406, -101, 477, -578, 164, 1273, 318, 355, -166, 464,
  -911, 710, 328, 478, 891, 14]

theorem fractionalNearFrameSubtreeG4R0032_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0032Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0032Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0032Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0032_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0032LowerBoundTable : List ℤ :=
  [279, 354, 1185, 33, 33, -231, 378, 790, 470, 2834, 1437, 414, -512, 1695,
  2274, 152, 3508, -91, 2390, 100, 1108, 295, -751, 1311, 2956]

def fractionalNearFrameSubtreeG4R0032LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0032Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0032LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
