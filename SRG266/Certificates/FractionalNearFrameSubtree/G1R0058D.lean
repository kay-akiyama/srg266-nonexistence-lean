import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0058`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0058Mask : ℕ := 745363205638417

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0058Witness : Array ℤ :=
  #[41, 62, 86, 140, 83, 122, -162, -185, -138, -152, -160, -190, 139, 118,
  73, 124, -3, 24, 50, 22, 54, 36, 33, 30, 34, 9, 67, -44, -25, -37, -11,
  -85, -168, -109, -27, 21, 38, 152, 184, 175, -43, -126, -170, -98, 168, 0,
  33, -32, 3, -67, 44, 42, -22, -4, 27, 54, 23, 11, 12, -108, -16, 81, 76,
  -30, -15, -27, 114, 35, -1, -39, -42, 23, -4, 31, -4, -31, 35, -37, 14,
  -14, -12, 21, -77, -26, 29, -4, -82, -7, 18, -58, -18, 48, 63, 15, 23,
  -25, 40, -87, 7, -34, 24, 2, -35, 23, 33, 4, -31, 29, 24, 9, 72, -43, 34,
  4, 65, -19, 35, -64, 9, -50, 12, 40, -46, -11, -25, 34, -24, 31, 53, 59,
  -28, 72, -28, 78, -11, 8, -6, -13, 93, -9, -40, 36, 30, -45, 20, -17, 66,
  63, 56, 59, 37, 16, 49, 74, -56, -34, -80, -20, -44, -7, -64, 56, -40, -8,
  -19, 59, 72, 22]

theorem fractionalNearFrameSubtreeG1R0058_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0058Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0058Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0058Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0058_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0058LowerBoundTable : List ℤ :=
  [11, 110, 2, 54, 84, 253, 2, 1, 105, 321, 159, -38, 50, 119, 9, 148, -235,
  55, 10, -67, 26, 98, -237, 154, 161]

def fractionalNearFrameSubtreeG1R0058LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0058Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0058LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
