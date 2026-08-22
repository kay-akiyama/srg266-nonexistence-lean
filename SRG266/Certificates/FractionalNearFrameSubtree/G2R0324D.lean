import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0324`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0324Mask : ℕ := 5390514286799280

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0324Witness : Array ℤ :=
  #[56, -47, 89, -51, -37, -7, 29, 13, -29, -104, 37, 163, 46, 184, -5,
  -157, 0, -37, -95, 100, 82, 116, 3, 136, 35, 3, -108, -38, -33, -29, 0,
  75, 131, 18, -162, -17, 116, 67, -79, -207, -84, -246, -92, 30, 181, -71,
  148, 39, 84, 37, 142, 138, 8, 0, 6, -44, 49, 190, -25, 104, -16, 256, -26,
  52, 67, 90, 0, -109, -96, 202, -105, 152, 44, 52, 309, 230, 39, 38, 92,
  249, -124, 185, -173, 152, 226, 25, 53, 18, 215, -9, 7, 8, 43, 113, 101,
  -1, 101, 36, 39, -55, -24, -20, -30, 161, 14, 135, 37, -51, 266, -3, 154,
  -59, -13, -107, 12, 41, 56, -61, 58, 105, 10, -131, 14, -4, -98, -8, 302,
  -86, 83, 94, -2, 91, 131, 27, -47, 240, -5, 126, -165, 137, 112, 188,
  -232, 91, -171, 156, -107, -70, 19, -131, 90, 45, 131, -115, -79, -210,
  268, -40, -96, -28, 51, -85, -139, -226, 51, 124, 177, -41]

theorem fractionalNearFrameSubtreeG2R0324_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0324Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0324Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0324Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0324_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0324LowerBoundTable : List ℤ :=
  [211, 111, 351, 668, 142, -19, 199, 302, 565, -354, -53, 30, 382, 503,
  532, 760, 455, 431, 194, 701, 1062, 9, 532, 627, 154]

def fractionalNearFrameSubtreeG2R0324LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0324Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0324LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
