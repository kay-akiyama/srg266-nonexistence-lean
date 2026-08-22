import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0016`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0016Mask : ℕ := 828598669509194

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0016Witness : Array ℤ :=
  #[25, 30, -67, 40, 86, -1, 69, 19, 23, 16, -3, 7, 13, -49, -85, -111, 38,
  -45, -58, -52, -69, 4, -8, 16, -16, -42, 53, 54, 32, 54, 3, -7, 52, 0,
  -13, 74, 24, 77, 48, 32, -29, 41, -25, 15, -120, 8, 64, 26, 54, -51, -31,
  40, 33, 44, -2, 29, -65, -5, 28, -48, -19, -33, 20, -11, -35, 51, -18, 2,
  11, -23, -33, 36, 56, 51, 75, 27, 10, 39, -23, -72, 35, 7, -18, -43, -7,
  52, -11, -72, 17, -16, -29, 2, 54, -87, -65, -23, 40, 5, 31, 24, -69, 32,
  18, 47, -26, 35, -91, 88, -34, -26, -76, -23, 27, -46, -12, -56, 8, -10,
  12, 44, 0, 3, -39, -9, -27, 25, -4, -45, -17, 80, 5, 15, 18, 36, -52, 17,
  0, 42, 0, 2, -26, 0, -29, 13, -61, -20, 10, -30, 25, 30, 25, 12, 25, 36,
  -65, -1, -26, -55, -37, -8, -36, 55, 4, 63, -11, 86, 77, -13]

theorem fractionalNearFrameSubtreeG3R0016_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0016Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0016Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0016Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0016_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0016LowerBoundTable : List ℤ :=
  [-47, 3, 56, -39, -50, 2, 107, 36, 46, 0, -25, -104, 65, 183, 234, -57,
  10, -91, -76, 10, -162, -34, 194, 113, 255]

def fractionalNearFrameSubtreeG3R0016LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0016Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0016LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
