import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0067`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0067Mask : ℕ := 5023447612301714

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0067Witness : Array ℤ :=
  #[-272, -377, -513, -1528, -1252, -813, 0, -219, 372, -493, -456, 1732,
  698, 1032, 935, 148, -89, -978, -185, 179, -210, 1046, 407, 873, 806, 721,
  -640, -253, -384, -195, 0, 499, 516, 28, -278, 216, -525, -673, -651,
  -128, 126, 413, 244, -287, -1146, -436, 264, 788, 573, 758, -34, 496, 379,
  581, -5, -785, -288, 84, -631, 768, 592, 484, 47, -29, -149, 162, 652,
  550, 391, 82, 367, -86, 83, -416, 123, 450, -379, -112, -482, 105, -372,
  482, 9, 1021, -36, 781, 876, 249, -186, 304, 480, 85, 364, 295, 585, -464,
  196, -559, 165, 69, 861, -738, 244, -250, 856, -562, -131, -867, 836, 853,
  -469, -616, -149, -497, 229, -117, -4, -535, 204, 82, -233, 274, -311,
  -449, 94, -153, 147, 960, -656, -308, -620, 270, 300, 426, 411, -247, 39,
  567, 362, 147, -95, 30, -114, 298, 530, 245, -433, 417, 953, 386, 778,
  643, 118, 494, 304, -817, 636, 340, -1060, 364, -126, -310, -818, -344,
  345, 929, 631, 530]

theorem fractionalNearFrameSubtreeG5R0067_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0067Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0067Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0067Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0067_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0067LowerBoundTable : List ℤ :=
  [589, 941, 1098, 662, 1412, 958, 476, -92, 31, 3685, 1238, 203, -242,
  3113, 2957, 1785, -2412, 2310, 769, 1574, 2566, 819, 1548, 1088, 1847]

def fractionalNearFrameSubtreeG5R0067LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0067Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0067LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
