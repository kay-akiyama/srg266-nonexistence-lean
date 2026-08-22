import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0084`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0084Mask : ℕ := 2479043467054226

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0084Witness : Array ℤ :=
  #[25, -31, -15, 0, -50, -1, 33, 48, -34, 34, 48, 18, -22, -19, -27, -63,
  30, -2, 49, -15, -44, -61, -26, -41, -92, -106, 82, 26, 61, 89, -15, -4,
  13, -2, 19, -17, -27, 12, -51, 59, -53, -32, 55, -32, -78, 0, 23, 35, 30,
  -52, -10, -41, 34, -7, 10, 12, -8, 18, -50, 0, -101, 54, -6, -41, -55, -7,
  33, 13, -16, -68, 23, 112, -2, -9, 57, -73, 54, 38, -5, 35, 75, 17, 52,
  42, 65, 24, -14, -27, -54, 80, 58, -39, 47, 70, -39, -30, 48, -42, 51, 59,
  -26, -22, 0, -13, 0, 7, -45, -51, 65, 15, 17, -14, 0, 4, -21, 41, 7, -84,
  -41, 47, -40, 63, 11, 24, 12, -18, 17, -35, 39, -2, 34, 58, -61, 40, 64,
  69, -19, 26, -1, 31, 54, 50, -3, 47, 9, -18, 19, 21, 13, 34, -90, 85, -25,
  -34, -75, 2, 0, -11, -31, 9, 87, -55, -55, -100, -27, -72, 17, 11]

theorem fractionalNearFrameSubtreeG3R0084_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0084Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0084Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0084Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0084_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0084LowerBoundTable : List ℤ :=
  [-39, 26, 2, 1, 2, 1, 1, 25, 13, 10, -2, 228, -176, 240, -56, 197, 108,
  177, 9, -87, 194, 12, 21, -13, 77]

def fractionalNearFrameSubtreeG3R0084LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0084Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0084LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
