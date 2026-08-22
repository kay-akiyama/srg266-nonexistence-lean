import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0062`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0062Mask : ℕ := 969068659545226

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0062Witness : Array ℤ :=
  #[37, -10, -31, -15, 48, -1, 5, -17, -8, 57, -24, -17, 20, 8, -42, -27,
  -4, -33, -57, -11, -55, 33, -36, 51, 15, -25, 31, 42, 56, 5, -7, 48, 2,
  29, 41, 24, 15, -20, -51, -13, 12, -65, -78, -55, 59, 52, 91, -40, 47, 22,
  0, 19, 0, 16, -8, -17, -33, 30, 50, 70, -14, -10, -27, 35, 4, -15, 5, 11,
  -16, 67, 41, 22, 62, 15, -25, 52, 90, -52, 15, -4, -4, -11, -22, 24, 66,
  23, 1, -53, -12, -86, -19, -51, -50, 12, 13, -59, 42, 36, -8, -41, 4, 60,
  28, 45, 56, -45, 39, -32, 12, 24, -39, 63, -86, -60, -69, 45, -92, 7, 14,
  -11, -55, 7, -4, 57, -41, -4, 18, 18, -47, -25, -48, 20, 43, -18, -2, -4,
  45, -9, 23, -2, 9, -23, -26, -63, 4, 2, 69, -25, 65, 35, 48, 44, -71, 3,
  -28, -25, -56, -44, 4, 91, -51, -3, 30, 89, 20, 68, -23, 0]

theorem fractionalNearFrameSubtreeG3R0062_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0062Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0062Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0062Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0062_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0062LowerBoundTable : List ℤ :=
  [-38, 0, 85, -22, 0, 32, 43, 2, -4, -68, 184, -44, -93, 344, 172, -97, 57,
  -61, 37, 69, 11, 8, 154, 213, 140]

def fractionalNearFrameSubtreeG3R0062LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0062Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0062LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
