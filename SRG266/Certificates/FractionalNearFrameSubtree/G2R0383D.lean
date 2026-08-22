import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0383`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0383Mask : ℕ := 5739191559924120

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0383Witness : Array ℤ :=
  #[33, 15, 10, -60, -42, 45, 32, 68, -6, 3, -17, -50, -32, -34, 32, -64,
  -53, -53, -43, 16, 44, 20, -16, 47, -2, 33, 2, 42, -14, 21, 21, -40, 13,
  10, 18, 0, -23, 36, -28, -35, -28, -53, -59, -58, -4, -5, -3, 14, 9, 3,
  27, 31, 43, 20, 51, -8, -62, 31, 9, 12, -30, -15, 23, 11, 28, -37, 44,
  -50, -90, 7, 16, -12, -34, 25, 0, 9, -7, -41, 30, 30, 34, 94, 47, -17, 49,
  28, 11, 96, -50, 42, -49, -4, -17, 78, -60, -22, 28, 9, 24, -29, -33, 45,
  5, 16, 5, -16, -19, 22, 33, 19, 24, -15, 43, 7, -65, -30, -5, 46, 22, 22,
  -2, 29, -35, -66, 13, 6, 2, 33, -15, -26, -34, 42, 47, 26, -15, 11, -39,
  37, 70, 33, -5, 60, -20, 32, 50, -13, 17, -45, -19, -26, 6, 0, -72, 0,
  -12, 32, 0, -14, 32, -34, -8, 22, 24, -44, 0, -26, -5, -6]

theorem fractionalNearFrameSubtreeG2R0383_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0383Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0383Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0383Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0383_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0383LowerBoundTable : List ℤ :=
  [-26, 41, 3, -27, 78, -31, 65, 26, 1, -143, 91, -54, 86, 83, -7, 19, 69,
  -146, 14, -8, -11, 288, 43, 152, 218]

def fractionalNearFrameSubtreeG2R0383LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0383Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0383LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
