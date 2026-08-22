import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0137`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0137Mask : ℕ := 6088460122162258

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0137Witness : Array ℤ :=
  #[167, 26, 78, -112, 102, 47, 56, -146, -271, -242, 234, -163, -33, 102,
  453, 85, -26, 68, 37, -41, 118, 116, 27, -142, 8, -88, 63, 61, -32, -61,
  -2, -48, -168, 20, 62, -157, -349, -53, 248, 22, 62, -169, 105, 515, 77,
  103, 76, 9, -73, -225, 207, 42, 86, -99, 102, 4, -360, 86, 167, -125, -32,
  -141, -58, -405, 360, 91, 20, 69, 40, -149, 25, 96, 40, -190, -183, 169,
  186, 103, 333, 80, 103, 107, 79, -238, 33, -64, 175, -184, -162, -68, -7,
  -184, 90, 35, 386, -18, 96, -105, -135, -110, -46, 154, -135, 35, 6, 323,
  71, -69, -162, 20, -421, 40, 55, -31, 192, -213, -308, 380, 239, 34, -207,
  385, -40, 169, 118, -336, -175, 203, -183, 215, 16, 0, -121, -179, -254,
  265, 320, -38, 94, -9, -45, 221, 177, -17, -175, -74, 42, -342, -235, 136,
  -40, 208, 145, -5, 330, 35, 70, -234, 81, -307, 234, 106, -64, -320, 168,
  14, -474, 282]

theorem fractionalNearFrameSubtreeG5R0137_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0137Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0137Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0137Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0137_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0137LowerBoundTable : List ℤ :=
  [-118, 2, 1, 2, 83, -296, 401, 163, 2, -320, 10, 363, 319, 490, 11, 383,
  47, 9, 731, 151, -186, 686, 561, -426, 464]

def fractionalNearFrameSubtreeG5R0137LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0137Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0137LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
