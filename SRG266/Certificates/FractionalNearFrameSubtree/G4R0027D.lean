import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G4R0027`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0027Mask : ℕ := 5363197145619473

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0027Witness : Array ℤ :=
  #[-11, -508, -602, 233, 38, -187, 166, 843, 604, 894, 768, -996, -324,
  -1177, -1497, -770, -602, 470, -383, -1244, -797, 422, 303, -19, 501,
  -424, 476, 965, 472, 349, -298, -775, -435, 306, 110, 347, 182, 108, 236,
  -262, 179, 303, -870, 899, 1047, -576, 290, -385, -126, -1056, -570, -99,
  -128, 1048, 298, -171, -480, 416, 677, 172, 508, -271, -472, 63, -206,
  967, 793, -733, -447, 703, 1007, 1000, -235, -956, 603, 1094, 689, -355,
  83, -190, -506, -321, 550, -434, 492, -696, 605, 361, 107, -766, 1020,
  -1068, 874, 110, -222, 684, -543, -831, 253, -144, 1457, 879, -274, 69,
  607, 213, 513, 321, -394, -1296, -394, 573, -252, -269, 219, -110, 132,
  -474, 409, -205, 0, -122, 399, -778, 651, 44, 506, -490, 124, 28, -1046,
  173, 1014, -935, 489, 319, 582, -211, 706, -420, 484, 427, 385, 187, -843,
  -135, 20, -1078, 231, 345, 1006, 644, -347, -331, -397, -277, -1098, 856,
  -46, 534, 256, -381, -54, 381, 217, 1347, 759, 570]

theorem fractionalNearFrameSubtreeG4R0027_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0027Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0027Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0027Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0027_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0027LowerBoundTable : List ℤ :=
  [74, 461, 1286, 1583, 32, -379, -703, 492, 31, 325, 19, 2246, 1917, 5359,
  2151, -340, -1235, 3629, 99, 2915, 101, -920, 1279, 100, 100]

def fractionalNearFrameSubtreeG4R0027LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0027Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0027LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
