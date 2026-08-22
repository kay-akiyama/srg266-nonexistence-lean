import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0085`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0085Mask : ℕ := 929966277108812

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0085Witness : Array ℤ :=
  #[87, 25, 49, 50, -3, -15, 36, 41, -90, -68, -21, -32, 67, 29, 56, 38, 32,
  54, 26, 98, 41, 67, -95, -26, 58, -15, -25, -44, -74, 33, 61, -23, 21, 75,
  15, 60, 17, 0, -52, 15, -24, 34, 76, -65, 34, -53, -67, 59, 56, 58, -21,
  -76, -103, 58, -59, 51, 30, -15, -30, 18, 41, 11, 57, 2, -51, -70, 45, 52,
  131, 99, -6, 20, 19, 0, 139, -6, -119, 60, 41, -62, -120, 68, -41, -78,
  -5, -80, -13, 44, 39, -78, -54, -48, -61, 28, -36, -59, -16, -21, 11, 16,
  -14, 3, 91, 72, 21, 130, 48, -31, -24, 12, 18, 63, 38, -7, 59, 180, -28,
  -70, -53, 60, -63, -28, -28, 19, 21, 38, 6, 38, -78, -50, -67, -29, 83,
  -18, 62, 96, 9, 68, 67, -2, -37, 67, 55, -2, 12, 29, 25, -32, 52, 8, -41,
  43, 12, 9, -1, 97, 22, -6, -25, -45, 29, 125, -3, 18, 5, 7, -29, 51]

theorem fractionalNearFrameSubtreeG1R0085_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0085Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0085Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0085Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0085_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0085LowerBoundTable : List ℤ :=
  [20, 103, 2, 33, -10, 178, 80, 207, 227, 228, 205, 298, 337, 127, 11, -63,
  1, 455, 5, 154, 34, 22, 11, 148, 482]

def fractionalNearFrameSubtreeG1R0085LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0085Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0085LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
