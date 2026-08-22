import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0056`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0056Mask : ℕ := 689213143435537

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0056Witness : Array ℤ :=
  #[59, 9, -16, -4, -64, 25, 139, 63, 6, 100, 3, -45, 46, 73, 0, 32, -68,
  -34, 63, -44, -41, -11, -51, 86, -6, 44, -55, 23, 28, -23, 17, 31, 68, 23,
  44, 0, -43, -59, 69, 38, 11, 24, -66, -2, -52, -53, 20, 1, -37, -1, -8,
  -34, 13, 0, 14, 29, -4, -48, 29, 20, 24, -1, 4, -41, 2, 0, 58, 6, -5, -17,
  5, 11, -7, -3, 25, -34, -19, -16, 5, -4, -18, -19, -15, 3, -29, -8, 37,
  65, -9, 41, 0, 78, -26, -26, 38, 27, 30, 46, 0, 45, 16, -40, 29, -43, 0,
  -81, -2, 27, 35, 36, 6, -11, -6, -21, -16, -43, 12, -9, -40, -15, -2, -7,
  29, -2, 45, -85, 12, 16, -24, 14, -12, 28, -38, 45, 4, 20, 2, -67, -13,
  -30, -6, 38, -48, -68, -50, 4, -8, 26, 45, -1, 6, 40, 2, 23, 38, -18, 48,
  24, -36, -4, 20, 76, 42, 15, -47, 41, 11, -21]

theorem fractionalNearFrameSubtreeG1R0056_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0056Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0056Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0056Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0056_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0056LowerBoundTable : List ℤ :=
  [3, 1, 7, -46, 2, 112, 281, 32, 138, 106, -6, -33, -111, 10, 16, 160, 50,
  75, 63, 5, -116, 9, -58, 86, 157]

def fractionalNearFrameSubtreeG1R0056LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0056Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0056LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
