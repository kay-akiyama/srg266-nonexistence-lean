import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0126`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0126Mask : ℕ := 1352162728673482

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0126Witness : Array ℤ :=
  #[-25, -478, -326, -571, 125, -1340, 308, 915, 1254, 0, 994, -282, -618,
  -112, -1132, 435, 394, 417, 429, 382, -1151, -501, -437, 478, -384, 282,
  623, -615, 684, -133, -249, -350, 0, -522, -793, 748, 941, -130, -1218,
  409, 80, 31, -885, -563, -854, -834, -1308, -1586, 1412, 642, 1065, 1506,
  452, -1227, -320, 216, 526, 210, 761, 13, -58, -160, -590, -266, 1463,
  -146, 1128, -492, -288, 96, 416, -359, -243, -309, -32, 296, -276, -717,
  265, -451, 54, -179, -510, 844, -118, 120, 205, -1025, -329, 1035, 237,
  -421, -95, -525, 979, 126, 712, 173, -1015, -191, -5, 428, 277, 767, 1915,
  886, 1186, -446, -77, 462, -296, 572, -99, 217, 575, 930, 855, 109, 748,
  -604, -746, -233, 907, 178, 479, 748, -1058, -213, 1108, 117, -601, 217,
  268, -981, 869, 379, -1028, -388, -485, -290, 594, -91, 567, 237, -641,
  -125, -444, 487, -295, -108, 540, 38, -476, 472, 180, -502, -47, 87, 0,
  -974, 171, 187, -330, -120, -501, 1150, -420, 617]

theorem fractionalNearFrameSubtreeG2R0126_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0126Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0126Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0126Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0126_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0126LowerBoundTable : List ℤ :=
  [-566, 31, 307, 1386, 950, -1285, -1256, 915, 1072, -1082, -1236, 2503,
  1424, 4250, -104, -1707, -1341, 1390, 1794, 4077, -1581, 1906, 3558, -684,
  -149]

def fractionalNearFrameSubtreeG2R0126LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0126Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0126LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
