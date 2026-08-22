import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0013`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0013Mask : ℕ := 265977398217225

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0013Witness : Array ℤ :=
  #[365, 296, 386, 507, 260, 260, -135, -73, 208, 37, -214, -187, -232,
  -322, -210, -86, -173, -315, -108, -33, -88, 93, -42, 135, -80, -26, 165,
  -46, 83, 199, 97, 215, 157, 73, -20, 284, 110, 48, -77, -73, 75, 82, 117,
  31, 47, 133, 10, 0, -26, -32, -80, 20, -20, 20, 25, 11, -34, 185, 19, 115,
  22, 39, 16, 24, -37, -4, -199, 39, 1, -12, 91, 181, 107, 0, 34, 178, 122,
  -4, 96, -200, 14, 18, 37, 60, 174, -98, -87, -43, -176, 124, 200, -47, 53,
  15, -151, 165, -119, 122, 6, 97, 74, 115, 20, 72, -123, -27, 46, -44, 77,
  -197, -41, 31, -22, 85, 95, 53, -15, -8, -170, -68, -46, 32, 89, 57, 156,
  -28, -86, -34, -71, 53, -56, -89, 90, -51, -107, -29, 26, -208, 22, -67,
  141, 181, 47, 59, 102, 67, 9, 71, 51, 48, 102, 16, -14, 58, -7, 42, -53,
  -123, 22, 25, 37, 37, -49, -29, 60, 138, -39, 115]

theorem fractionalNearFrameSubtreeG1R0013_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0013Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0013Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0013Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0013_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0013LowerBoundTable : List ℤ :=
  [179, 136, 169, 233, 447, -24, 423, 385, 278, 81, 384, 124, -38, 502, 786,
  97, 668, 451, 149, 214, 322, -177, 799, 311, 9]

def fractionalNearFrameSubtreeG1R0013LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0013Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0013LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
