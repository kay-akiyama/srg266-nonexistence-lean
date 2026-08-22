import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0182`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0182Mask : ℕ := 1388148206178544

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0182Witness : Array ℤ :=
  #[-348, 433, -243, -116, 64, -271, 360, -438, 486, 129, -254, 273, -237,
  -135, 957, 881, 925, 467, 408, -152, 323, -515, -652, -826, -157, -743,
  83, -561, 154, 71, 391, -456, -351, -16, 829, -128, -72, -917, -874, 299,
  251, 604, 176, 530, 216, 26, -293, -773, 3, 427, 10, -73, -359, -311, 75,
  -196, 365, -545, -46, 754, 113, -382, 130, -1255, -157, -378, -536, 430,
  -247, 530, 344, -741, 218, 15, 108, -111, -373, 457, 561, 489, -351, -428,
  57, -524, -221, 485, -817, -112, 120, -264, -58, 285, -269, 24, -75, -426,
  480, 67, -160, 166, 334, 305, 94, -114, -92, -637, -684, 0, 421, -134,
  -28, 3, 173, 163, 246, 426, -385, 825, -241, 852, -723, -656, 402, 0, -34,
  -476, 43, -595, 405, 403, -422, -614, -660, 268, 422, -17, -243, 38, 891,
  -152, 454, -168, -524, 697, 503, 444, 570, -837, 735, 418, 57, 479, -43,
  -198, 490, 68, -198, 425, 715, 158, 791, -122, -737, -425, -107, -519, 87,
  194]

theorem fractionalNearFrameSubtreeG2R0182_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0182Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0182Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0182Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0182_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0182LowerBoundTable : List ℤ :=
  [-660, 915, 209, 33, 737, -636, 32, 33, -641, -168, 527, -1499, 305, 99,
  1414, 717, -2470, 195, -663, 3442, 370, 2165, 663, -1736, 100]

def fractionalNearFrameSubtreeG2R0182LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0182Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0182LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
