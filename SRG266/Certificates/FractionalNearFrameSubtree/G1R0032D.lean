import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0032`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0032Mask : ℕ := 520931938017484

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0032Witness : Array ℤ :=
  #[29, -29, -56, -49, -105, 61, 50, 86, 81, 102, -72, -7, -27, 41, 11, -68,
  6, -2, -18, 29, -2, -40, -26, 13, 74, 23, -19, 1, 64, 27, -10, -40, 40,
  -41, -54, -67, 25, 74, 41, -60, -38, -77, -79, -139, -101, -138, 2, -9,
  95, 74, 21, 60, -61, 11, 86, 102, 157, 35, 55, -102, 41, 91, -50, -63, 88,
  -97, 54, 70, -6, 64, 54, -67, -50, 31, 54, -124, 67, -39, -5, 17, 32, -28,
  8, 78, 50, -29, -13, -29, 12, 68, -42, -7, -23, -6, 20, 34, 24, 18, 47,
  14, 109, 45, 14, 27, 78, -43, 60, 27, 62, 26, -39, 56, -20, 55, 26, -28,
  -84, 13, 34, -72, 36, -39, 103, 34, 85, -15, -95, 28, 85, -90, 60, -100,
  -20, 15, -7, -21, 25, 49, 56, 47, -45, 18, 25, 14, 9, -15, 29, 74, -13,
  -95, 8, 58, -10, -57, 32, 64, -7, -85, 26, -28, 1, 45, -51, 44, 29, -43,
  -59, -16]

theorem fractionalNearFrameSubtreeG1R0032_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0032Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0032Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0032Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0032_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0032LowerBoundTable : List ℤ :=
  [20, 2, 33, 131, 43, 2, 133, -35, 93, 154, 208, -4, 181, 264, 271, 9, -40,
  -7, 309, 110, 109, 165, 10, -6, 10]

def fractionalNearFrameSubtreeG1R0032LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0032Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0032LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
