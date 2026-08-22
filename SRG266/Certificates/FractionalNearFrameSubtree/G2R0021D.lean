import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0021`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0021Mask : ℕ := 690062331994633

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0021Witness : Array ℤ :=
  #[238, 915, 383, 954, 1060, 628, 133, 0, -394, -233, 163, -62, -453, -293,
  -414, -200, -901, -504, -98, -410, -99, 181, 326, -18, -495, -456, -261,
  -335, 345, 238, 664, 282, -211, -215, 970, -21, 150, 362, 59, 379, -354,
  -49, 427, -145, 218, -436, 20, -355, 348, 416, 516, 107, 70, 58, 591, 227,
  -163, -61, -1, -156, 633, -95, 24, 1084, -129, 150, -2, 289, -335, -787,
  -130, 326, 200, -79, 269, 68, -45, -159, 412, 254, 443, 296, -38, -889,
  101, -494, -707, 313, 768, 300, -344, -300, -554, -285, 116, -204, -583,
  -434, -116, 224, -343, 28, -36, 151, 65, -172, -271, -313, -330, 63, -67,
  313, 242, -313, 114, -267, -112, 71, -189, -138, 170, -256, -59, -489,
  -143, -190, 369, 420, -48, 29, 168, 301, -121, -212, 354, -27, -389, 36,
  273, -732, 41, 177, 198, 129, -237, -86, -463, 20, 16, -67, -116, 348, 91,
  -546, -161, 150, 408, 287, -215, -170, 161, 568, -29, -53, -165, 79, 435,
  -137]

theorem fractionalNearFrameSubtreeG2R0021_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0021Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0021Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0021Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0021_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0021LowerBoundTable : List ℤ :=
  [-296, -225, -846, 32, 31, -322, 1757, 289, 306, -268, 631, -843, 397,
  572, -169, 786, 1059, 1000, -839, 760, 432, 1811, 260, 947, -730]

def fractionalNearFrameSubtreeG2R0021LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0021Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0021LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
