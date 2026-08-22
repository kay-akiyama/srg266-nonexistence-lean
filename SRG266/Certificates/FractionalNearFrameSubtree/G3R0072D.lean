import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0072`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0072Mask : ℕ := 2338379209085443

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0072Witness : Array ℤ :=
  #[88, -643, -298, -370, -83, -20, 26, 808, -510, 698, 377, -122, 56, 684,
  -134, 736, -100, 589, 917, -435, -29, -543, -727, -42, 129, 117, 819, 53,
  -159, 528, -574, -75, -274, 0, 1154, -102, -259, -173, 543, 62, 608, 342,
  777, 584, 22, -605, 492, 552, 289, 600, -525, -472, -492, 138, -819, 228,
  165, -19, 339, 176, 0, 46, -364, 133, 122, 308, 648, 430, -556, -86, -330,
  1007, 474, 460, 1013, -396, 208, -201, 582, -100, 162, -11, -399, 201,
  674, 906, 198, -115, -94, -295, -738, -131, -155, 613, 729, 715, 1117,
  696, -290, -166, 154, 153, -752, 278, 146, 27, 1085, -382, 187, 458, 365,
  259, 715, 942, 0, -1043, -431, 551, -535, -824, 259, -211, 795, 262, 221,
  630, -886, -620, -535, 488, 790, -551, -39, 623, -1, 378, 513, -464, -227,
  -219, -152, 266, 568, 37, 349, 584, 541, -612, 192, 471, -602, 1046,
  -1857, 245, 474, 208, -223, -316, -1063, 535, -1055, 55, -25, 304, -730,
  -289, 653, 442]

theorem fractionalNearFrameSubtreeG3R0072_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0072Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0072Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0072Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0072_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0072LowerBoundTable : List ℤ :=
  [471, 33, 1343, -215, 1565, 2366, 447, 706, 854, 1629, 6, 2453, 231, 4627,
  4358, 2338, 1508, 418, 100, -55, -634, 3312, 2118, 1474, 100]

def fractionalNearFrameSubtreeG3R0072LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0072Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0072LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
