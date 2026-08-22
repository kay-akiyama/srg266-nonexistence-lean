import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0523`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0523Mask : ℕ := 6771572024646673

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0523Witness : Array ℤ :=
  #[-110, -31, -57, -91, 32, -101, 128, 90, 138, 104, 105, 157, -71, 34,
  -33, -65, -1, -64, 44, -7, -29, 17, 30, -43, -9, -45, -8, -26, 43, 17, 9,
  92, -64, -46, -47, 46, 84, -78, -115, -25, 19, 57, 78, 64, 34, 41, -49,
  -21, -9, 13, -39, 25, -32, 32, 39, -1, 60, 51, -14, -96, -11, 19, 18, -7,
  0, 45, 28, 37, -17, -21, -17, 28, 12, -13, -29, 33, 7, 39, 37, 40, -8,
  -28, 26, -2, -24, 52, 19, -59, 15, -15, 42, -50, 70, 44, -39, -71, -75,
  15, -26, 22, 69, 58, 45, 30, 62, 0, -9, -31, -27, 18, 0, -44, 12, 37, -46,
  36, 19, 80, -16, 32, 35, 51, 42, -20, 43, 33, 12, -8, -25, -50, -5, -5,
  29, 11, 28, -18, -4, -7, 3, -9, -5, 88, 17, 10, 5, -53, 42, 20, 40, 31,
  23, -39, -36, -32, 75, 0, 15, 42, 7, -56, -32, -71, -18, -32, -64, -3,
  -29, -59]

theorem fractionalNearFrameSubtreeG2R0523_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0523Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0523Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0523Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0523_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0523LowerBoundTable : List ℤ :=
  [16, 1, -43, 2, 180, 2, 2, 200, 3, -51, 58, 69, 126, 60, 194, 124, 88,
  123, -95, 51, 72, 129, 101, 94, 199]

def fractionalNearFrameSubtreeG2R0523LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0523Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0523LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
