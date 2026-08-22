import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0160`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0160Mask : ℕ := 1866789845110034

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0160Witness : Array ℤ :=
  #[104, 101, 136, 105, 164, 103, -103, -54, -85, -72, -91, -40, -87, -24,
  -74, -38, -76, 49, 9, -9, -31, 26, 7, -62, 26, -81, -25, -24, 8, 76, 50,
  117, -5, 43, 9, -40, -2, 1, 13, -28, 12, -44, -21, -3, -8, -13, -36, 46,
  17, -100, 12, -39, 7, 27, -22, -70, -24, -19, -37, 61, 46, 22, -18, -11,
  50, -39, 25, -3, -71, 45, 8, -6, 39, 47, -56, -18, 33, -136, 22, 2, -30,
  4, 25, -30, 23, -25, -88, -19, -45, 51, -3, 73, -52, 43, -40, 5, 39, 4,
  -98, -3, 34, 6, -9, -16, 8, 48, -54, 82, -41, -5, 69, 49, 40, 57, 1, 36,
  83, -57, 15, 15, 13, 40, -21, 20, 61, 25, 51, 34, 73, -47, 13, 39, 53, 52,
  15, 45, 4, 12, 3, -10, -28, 68, -10, -13, -21, 63, -32, -39, 12, 23, -12,
  31, 10, -65, 9, 13, 72, 36, -45, -16, -37, 24, 10, 29, 12, 55, -29, 41]

theorem fractionalNearFrameSubtreeG1R0160_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0160Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0160Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0160Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0160_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0160LowerBoundTable : List ℤ :=
  [-3, 138, 2, 77, -27, 109, 2, 3, 1, 328, 161, 183, 162, -30, -9, -2, 8,
  155, -90, 46, 106, 11, 116, 9, 123]

def fractionalNearFrameSubtreeG1R0160LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0160Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0160LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
