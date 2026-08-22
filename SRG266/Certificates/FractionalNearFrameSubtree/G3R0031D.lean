import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0031`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0031Mask : ℕ := 954024280687178

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0031Witness : Array ℤ :=
  #[-168, 857, 816, 1138, 764, 1226, -620, -173, -1664, -266, -1769, -171,
  418, 639, 748, 231, 105, -447, 327, 378, 65, 173, 765, 738, 22, -300, 369,
  285, 424, -457, 384, 185, 498, 338, 98, 1693, 723, -1143, -1421, 1344,
  1061, 887, -1027, -1063, -676, -396, -261, -630, 151, -278, 497, 1161,
  916, 483, 119, -275, 1320, 160, 439, 428, 4, -3, 77, 189, -225, -518,
  -303, 188, 323, -306, 4, 528, 26, -404, -76, -206, 29, 214, 441, 458, 250,
  1313, -8, -526, -664, -401, -366, -24, 350, -56, 693, -65, 338, 297, 198,
  5, -360, -146, 517, -146, -394, -52, -78, 146, 231, -69, -304, 49, -498,
  243, 650, -51, -168, 217, 733, 706, -19, -3, -127, -406, 364, -10, 657,
  61, -620, -503, 364, 29, -213, 845, -654, -140, 166, 293, -26, -39, 668,
  196, 15, 493, 214, -160, -203, -81, -243, 252, 537, -191, 43, 105, 998,
  77, 252, 521, -469, 107, 346, -193, 543, 93, -299, -317, 12, -336, 41,
  -74, 194, 0]

theorem fractionalNearFrameSubtreeG3R0031_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0031Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0031Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0031Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0031_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0031LowerBoundTable : List ℤ :=
  [769, 863, 32, 1188, 33, 849, 1572, 2719, 1129, 1308, 1436, 862, 101, 999,
  101, 638, 390, 2096, 2603, 3502, 287, 1668, 2714, 2526, 2848]

def fractionalNearFrameSubtreeG3R0031LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0031Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0031LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
