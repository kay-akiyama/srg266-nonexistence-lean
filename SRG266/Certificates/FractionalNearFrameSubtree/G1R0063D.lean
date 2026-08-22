import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0063`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0063Mask : ℕ := 805709570165400

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0063Witness : Array ℤ :=
  #[68, -78, -37, 51, 32, 42, 45, 18, 100, 15, -18, -29, 0, -100, 45, -44,
  44, -6, 15, 5, -5, 44, -17, 102, -80, -78, 2, -19, 92, 77, 49, -43, 23,
  -72, -125, 9, 26, -29, 39, -9, -90, -77, -68, -68, -17, -84, -57, -25, 98,
  71, -35, -29, -21, 102, 182, -65, -39, 61, -8, 39, -25, 22, 29, 50, -9,
  37, 11, 31, -29, 8, 25, -17, -36, -7, -60, -51, 18, 53, -77, -46, -46, 51,
  42, -14, 62, -7, 62, 16, -4, 50, 26, 50, 4, 11, -53, 53, -2, -7, -86, 12,
  35, -78, 28, 15, -4, 29, 29, 36, -4, -65, -68, -36, -33, -69, 0, -21, 15,
  -9, -34, -16, -15, -26, 4, -16, -32, -3, -38, 36, 22, -82, -92, -80, -68,
  -26, 27, 12, 4, 12, -36, -55, -25, -59, 90, -93, -92, -28, 34, -90, 27,
  52, -96, 15, 8, 7, -6, -4, 124, -33, -39, -39, 10, 0, -68, 14, 164, 53,
  12, 8]

theorem fractionalNearFrameSubtreeG1R0063_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0063Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0063Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0063Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0063_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0063LowerBoundTable : List ℤ :=
  [-123, -108, 62, -4, -42, -52, -49, 8, -60, -251, -102, -269, 11, -102, 9,
  -56, 244, -63, 82, 15, -139, -26, 281, -90, 22]

def fractionalNearFrameSubtreeG1R0063LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0063Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0063LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
