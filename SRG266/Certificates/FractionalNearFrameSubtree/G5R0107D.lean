import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0107`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0107Mask : ℕ := 5776752850603011

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0107Witness : Array ℤ :=
  #[1038, 673, 140, -451, 12, -402, -289, -295, 0, -67, -1137, 886, 199,
  -191, 93, -1188, -386, -52, -184, -898, -610, -620, 417, 849, 825, 279,
  -22, 8, -166, 570, -495, 159, 1011, 272, -487, -83, -212, -669, -1161,
  -600, -916, 1288, 681, 1130, 270, 27, 464, 1335, -128, -301, -153, -339,
  975, -815, -349, -145, -958, 109, 578, 575, 149, 465, -389, 126, -907,
  -255, -563, 30, 628, 248, -323, 228, 1408, -92, -644, 843, -125, -184,
  258, -69, 18, -38, 574, 36, 511, 1301, -727, -625, 793, 462, 63, 1158,
  256, -553, -233, -444, -173, 88, 393, 831, 1028, -461, -45, -472, -130,
  91, -465, -459, -441, -1092, 459, 441, 217, 679, 97, 211, -545, -405,
  -1349, 599, -80, -552, -572, 31, -47, 216, 391, 194, 36, 735, 486, -277,
  -138, 625, 214, -85, -409, 148, 379, -293, 630, 286, -21, 234, 782, 230,
  392, 326, 544, 1066, 120, 448, -32, -633, -548, 126, -265, -105, -198,
  -221, 1019, -573, 597, 388, 1177, 391, -221, 0]

theorem fractionalNearFrameSubtreeG5R0107_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0107Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0107Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0107Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0107_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0107LowerBoundTable : List ℤ :=
  [130, 1262, 1585, 32, -796, 32, 31, 1792, 31, 1001, 1872, 99, 302, 1253,
  2798, 2819, 716, 708, 2751, 91, -1217, 1081, -570, 2123, 2985]

def fractionalNearFrameSubtreeG5R0107LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0107Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0107LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
