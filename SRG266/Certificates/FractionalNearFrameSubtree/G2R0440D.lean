import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0440`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0440Mask : ℕ := 5786353792617048

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0440Witness : Array ℤ :=
  #[137, 50, 102, 55, -32, 8, -50, -142, -15, -44, 34, 101, 30, 50, 41, 28,
  5, -60, 26, 64, -10, 148, -49, -23, -19, 44, -136, 9, 13, 12, 126, -7,
  -158, 15, 48, 24, 14, 46, -149, 0, 0, -101, 8, 52, -55, 50, -52, -17, 57,
  28, 107, 70, -65, -33, 41, 104, -11, 0, 129, -59, -32, 0, 63, -57, -129,
  0, 0, 90, -28, 0, 53, 91, -59, -2, 118, 73, 101, 13, 31, -39, 51, -7, -24,
  -5, 35, 115, 54, -19, 53, -28, 61, -13, -45, -41, 8, 73, 51, 33, -16, -28,
  87, 26, 89, 69, -128, 96, 14, 14, 2, 77, 156, -93, -53, -90, 126, 114,
  -74, 22, 24, -63, 106, 1, 1, -73, -18, -44, -6, 71, -27, 133, -35, 116,
  100, -21, 10, 72, 28, 71, 60, 70, -6, -34, 6, 54, 80, 31, 12, 49, 132, 4,
  -23, -46, -32, 17, -145, 152, 34, 99, -19, 60, -81, 179, 58, 157, -24, 62,
  -35, 16]

theorem fractionalNearFrameSubtreeG2R0440_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0440Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0440Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0440Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0440_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0440LowerBoundTable : List ℤ :=
  [128, 307, 300, 90, 298, 220, 3, 82, 288, 193, 554, 38, 407, 213, 199,
  -24, 530, 179, 286, 370, 484, 154, 172, 97, 134]

def fractionalNearFrameSubtreeG2R0440LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0440Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0440LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
