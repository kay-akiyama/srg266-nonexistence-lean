import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0122`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0122Mask : ℕ := 5860163214772874

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0122Witness : Array ℤ :=
  #[254, -45, 699, 355, 332, 59, -268, -580, -557, 0, -872, -373, 125, -139,
  50, -20, 93, -141, -192, 86, -68, 551, -208, 670, -190, -324, -874, -64,
  -215, 493, 30, -63, -563, 250, 632, -3, 427, 102, 268, 1154, -1114, -474,
  -316, -293, -84, 0, -370, 88, -65, 906, 1132, 617, -11, -468, -286, 109,
  741, 512, -734, -238, -120, 555, 280, -220, -423, 260, 469, -701, 102,
  174, 66, -290, 399, 332, 288, 696, -347, -610, -88, -325, -662, 45, -732,
  248, 614, -30, 28, 776, -203, -383, 832, -48, 461, -170, -632, -241, -261,
  -90, 65, 670, -198, -685, 405, -61, 675, -714, -296, -208, 163, -285, 499,
  -169, -547, -532, -62, -259, -511, 115, -334, 234, -654, -931, -802, 903,
  -64, -190, -353, 416, -184, 317, 670, 354, -183, -454, -210, -725, -553,
  552, 436, 339, 224, 78, -329, 128, -910, -28, -571, -491, 654, 350, 697,
  266, 503, 337, 287, 440, 329, 591, 630, -296, -9, 801, -144, -146, 68,
  136, 368, 177]

theorem fractionalNearFrameSubtreeG5R0122_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0122Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0122Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0122Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0122_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0122LowerBoundTable : List ℤ :=
  [-669, 167, -178, 32, 33, 599, 32, -492, 870, 2314, 2274, -3239, 1111,
  948, 100, 206, 1745, -938, 907, 990, -253, 14, -696, 444, -467]

def fractionalNearFrameSubtreeG5R0122LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0122Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0122LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
