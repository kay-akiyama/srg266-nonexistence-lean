import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G4R0039`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0039Mask : ℕ := 5464043208509784

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0039Witness : Array ℤ :=
  #[-165, -173, -292, -288, -350, 130, 221, 23, 110, -38, 191, 322, 171,
  151, -55, 165, 110, 137, 77, 76, 216, -177, 0, -123, -105, -347, -3, 27,
  -79, 86, -152, -2, 120, -83, 108, 242, -193, 240, -2, -34, 149, 0, 5, -88,
  44, -82, -61, 68, 185, 169, 120, -87, 133, 227, -201, -228, -74, 229, 64,
  32, -78, -78, 164, -11, 42, -30, 97, -93, 200, 50, -35, 79, 99, 18, -16,
  163, 178, -28, -61, 17, 209, 161, 7, 63, -8, 146, 152, -71, -149, -19, 8,
  -99, 33, -100, 23, -152, 35, 24, -22, -71, 17, 235, 71, 11, 159, 40, 119,
  -169, -104, 6, 81, 105, 119, 40, 6, 0, -62, -170, -58, 91, 33, 0, -254,
  -95, 46, -75, 39, 83, -95, -47, 9, 14, -26, -5, 31, 38, -67, -116, 173,
  68, -118, 65, -89, -198, 98, -81, -17, 240, 32, 139, 163, -38, 179, -10,
  -41, -149, -88, 41, 28, -104, -167, 71, -113, -33, 44, -83, 253, -27]

theorem fractionalNearFrameSubtreeG4R0039_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0039Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0039Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0039Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0039_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0039LowerBoundTable : List ℤ :=
  [-10, -39, 225, 222, 236, 15, -8, 208, 9, 376, -577, 9, 7, 747, 289, 113,
  218, 429, 146, 278, 257, 529, 79, 202, 540]

def fractionalNearFrameSubtreeG4R0039LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0039Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0039LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
