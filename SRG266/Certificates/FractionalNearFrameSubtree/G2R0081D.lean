import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0081`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0081Mask : ℕ := 1002258153706580

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0081Witness : Array ℤ :=
  #[-74, -163, -265, -134, -478, 50, 508, -229, 293, -345, -50, 311, 38,
  248, -99, 350, 153, 113, -111, -35, 189, -32, -400, 260, -311, -337, 59,
  -105, 238, -142, 180, 357, 381, 147, -602, 463, 253, -604, -387, -550,
  -667, 245, 523, 67, 8, -20, 358, 111, 224, -324, -41, -45, 59, 404, 193,
  -311, -89, -446, -69, 316, 405, 328, 28, 250, 219, -151, 168, -120, 184,
  42, -187, 14, -55, -143, 12, 27, 213, -417, 2, -143, 22, 183, -337, 80,
  -321, 228, 101, -19, -208, -66, -126, 81, -13, 0, 130, -176, 106, 136,
  195, 304, 273, 59, 378, 149, 71, 75, 55, 265, -357, -111, -317, -260, 11,
  116, -3, -316, 215, -120, -65, 103, 111, 107, -191, -217, -87, -22, -17,
  47, -154, 225, -107, -81, -40, 39, 92, -300, -6, -32, -181, -79, 137, 100,
  -82, 136, 230, 21, 361, -75, 184, 185, 58, 246, -81, 35, -70, 84, 233, 13,
  229, -117, -83, -49, -243, -194, -41, 0, 4, 189]

theorem fractionalNearFrameSubtreeG2R0081_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0081Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0081Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0081Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0081_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0081LowerBoundTable : List ℤ :=
  [-348, 2, 275, 196, 2, 52, 479, 2, -1007, 1228, 341, -304, -901, 314,
  1209, 40, -948, 9, 581, 920, -753, 973, 735, 653, 1197]

def fractionalNearFrameSubtreeG2R0081LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0081Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0081LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
