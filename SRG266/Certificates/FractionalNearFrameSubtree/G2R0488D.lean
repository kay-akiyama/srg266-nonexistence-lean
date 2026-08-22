import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0488`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0488Mask : ℕ := 5811156001347084

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0488Witness : Array ℤ :=
  #[6, -46, 18, -71, -6, 0, 37, 62, -15, 78, 14, -23, -20, -71, -34, 35, -8,
  -29, -12, 15, -25, 11, 20, 21, -33, -66, 65, 54, 24, 44, -28, -26, -28, 5,
  -10, 37, -48, -35, 20, 24, 36, 23, 45, -12, 5, 20, 39, -16, -44, -59, 15,
  52, 48, 6, 60, 12, 19, -19, -4, -52, 3, 44, -3, 12, -45, -35, 23, 9, -34,
  -12, 20, 37, 49, 39, 23, -8, -5, 13, 26, -2, 39, 43, -51, -4, 50, -3, -24,
  6, 13, -25, -57, -36, -3, -7, -26, -3, 6, -16, -59, -6, 55, -12, 15, -56,
  -22, 42, 20, 29, -23, -46, -17, 18, -1, 51, -96, -16, 10, 60, -42, -35, 0,
  32, 6, -41, -34, -52, 11, -29, 15, 23, 2, 14, -7, -3, 5, 3, 50, -4, 38,
  46, -32, 19, 20, 6, -6, 56, 16, -29, -19, 12, -46, 36, 2, 23, -38, -31,
  -67, -6, -67, 15, -45, 29, -18, 38, 7, -7, -10, -24]

theorem fractionalNearFrameSubtreeG2R0488_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0488Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0488Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0488Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0488_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0488LowerBoundTable : List ℤ :=
  [-55, -47, 2, 1, 2, 8, -116, 31, 3, -54, -91, 102, 36, 33, 58, 199, -119,
  -21, -139, 100, 93, 40, 185, -30, 224]

def fractionalNearFrameSubtreeG2R0488LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0488Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0488LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
