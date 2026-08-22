import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0168`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0168Mask : ℕ := 2446911219878417

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0168Witness : Array ℤ :=
  #[-48, -25, -98, 0, -46, -114, 33, 120, 67, 144, 139, 72, -28, -89, -21,
  -90, -42, -46, -64, -38, -87, -51, -95, 75, -6, 26, -17, -9, 61, 122, 78,
  67, 23, -18, -13, -39, -93, 49, -5, 6, 61, 37, 2, -7, 41, -72, 50, 3, 12,
  -47, -17, -1, -15, -18, -8, 28, 3, -13, 53, 14, 13, -23, 10, -15, -4, 29,
  -32, -67, -1, 14, 33, 16, -15, 34, -46, 44, 35, 42, 10, 5, -9, -2, 28, 56,
  -53, -64, -57, -3, 4, -12, -17, -1, -51, -112, -5, 60, 30, 3, 25, 22, 45,
  2, 13, 35, 46, -46, 14, -86, -44, 60, -7, -74, -91, 2, -81, 61, 12, -14,
  1, 60, -26, -75, 31, 61, 11, -7, 5, -11, -42, 6, 58, -1, -72, -41, 24,
  -17, -8, -14, -7, 24, 34, -44, -19, 16, 73, 65, -21, -48, -66, 9, 20, -36,
  -66, 40, 74, 37, 44, -2, 19, 0, 15, 22, -46, 1, -5, 72, 37, 41]

theorem fractionalNearFrameSubtreeG1R0168_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0168Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0168Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0168Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0168_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0168LowerBoundTable : List ℤ :=
  [-53, 15, -13, 27, 1, -19, 65, 3, 1, 45, -47, 107, -12, -33, -124, 82,
  242, 10, -194, 20, 97, -162, -93, 36, 168]

def fractionalNearFrameSubtreeG1R0168LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0168Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0168LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
