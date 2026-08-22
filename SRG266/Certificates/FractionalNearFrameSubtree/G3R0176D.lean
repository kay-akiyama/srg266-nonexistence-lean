import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0176`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0176Mask : ℕ := 6865884506177938

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0176Witness : Array ℤ :=
  #[417, -150, -224, -465, -247, -732, 939, 1646, 872, 946, 558, -403, -679,
  249, -1150, -208, -999, -639, 1242, -1076, -447, 6, -421, -608, -960,
  1044, 1722, 1136, 364, 842, 843, -689, -381, -266, -156, 636, 630, 404,
  -869, -378, 729, -31, 651, -390, -793, 69, 82, -50, -213, -146, 776, -542,
  247, -109, 383, -238, 633, 297, -489, -508, -953, -894, -246, -407, -280,
  1285, -147, 1498, -1390, -95, 342, -312, 595, 545, -1207, -449, -352,
  -537, 627, -421, -636, 153, -99, 895, 185, 1262, -533, 437, -71, 341,
  1097, 152, 18, -165, 440, 396, -555, -45, -382, 402, -139, 82, -143, -63,
  1160, -846, 146, 654, -478, 472, 685, -443, -337, -605, -36, 583, 214,
  255, 605, -355, 259, 309, 224, 515, -96, 425, 794, 792, -950, 871, 436,
  192, -283, 421, -444, 1049, 865, 457, 253, -415, 85, 336, -425, -792, 330,
  510, 202, 0, 303, 150, 362, 124, -176, 363, -623, 647, 336, 64, -30, -595,
  -318, -744, 852, 777, -998, -752, -1009, -1309]

theorem fractionalNearFrameSubtreeG3R0176_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0176Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0176Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0176Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0176_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0176LowerBoundTable : List ℤ :=
  [-236, 32, -1147, 32, 91, 1465, 1231, 991, 33, 625, 1461, 3257, 101,
  -2127, 211, 99, -763, 3102, 1148, -871, -294, 1941, -672, 8720, 3013]

def fractionalNearFrameSubtreeG3R0176LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0176Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0176LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
