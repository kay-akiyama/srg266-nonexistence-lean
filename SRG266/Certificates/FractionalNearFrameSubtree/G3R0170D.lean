import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0170`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0170Mask : ℕ := 6857226894619304

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0170Witness : Array ℤ :=
  #[14, -82, 7, -28, 1, 33, -34, 10, -31, -34, 54, 58, 27, -36, 21, -42,
  -25, 13, 22, 66, -8, 46, 5, 3, 71, -1, -4, -29, -11, 25, 49, 10, 31, -94,
  -118, -1, 28, 14, -14, -7, 29, -49, -94, 75, 57, -33, 37, 28, 120, -1, 76,
  -52, -41, 54, -63, 30, 47, -17, -9, 46, 121, 61, 6, 11, -34, 26, 0, -66,
  5, -120, -26, 36, 84, 58, -16, -36, 9, -80, 29, -93, -36, 15, -60, 47,
  102, 13, -35, 6, 43, 37, 69, 56, 41, -10, 27, 10, -63, 17, 30, 58, -41,
  33, -78, 71, 33, 8, 49, -13, -55, -65, -1, -10, -25, 12, -28, -3, 61, -52,
  31, 37, 125, 37, -53, -10, 68, 85, 23, -14, 12, 20, 45, 34, 26, -16, 138,
  13, 33, -31, 42, 65, -18, 82, -116, 28, 28, -12, 95, 33, -11, 25, 11, -17,
  -74, 10, 32, 15, 14, -68, -44, 20, 0, 16, -4, 20, -30, 7, -34, -56]

theorem fractionalNearFrameSubtreeG3R0170_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0170Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0170Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0170Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0170_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0170LowerBoundTable : List ℤ :=
  [22, 168, 113, 3, 3, 165, 96, 111, 2, 10, 202, 163, 50, 88, 198, 259, 138,
  -94, 83, 270, -151, -70, 73, 289, 113]

def fractionalNearFrameSubtreeG3R0170LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0170Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0170LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
