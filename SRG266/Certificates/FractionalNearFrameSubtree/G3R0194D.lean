import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0194`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0194Mask : ℕ := 6867812034072084

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0194Witness : Array ℤ :=
  #[33, 28, 55, 60, 50, -10, 13, -9, 10, -63, -16, -32, 3, -24, -30, 2, -17,
  -2, -43, 21, -11, -19, 47, -14, 38, -41, 34, 19, -43, 33, 0, -33, 32, 10,
  -21, -10, -10, 20, -4, 4, -24, -32, 24, -21, 18, 19, 23, 72, -59, 6, -16,
  27, 31, -16, -31, 13, -81, 8, 40, 32, -18, 26, 38, -13, 49, 31, 23, -39,
  -31, -10, 0, 0, 100, -2, 2, -58, 49, -23, 6, 11, -10, -20, -80, -20, -1,
  33, -10, 35, -25, -28, -48, 2, -1, 9, -7, 32, -66, 77, 21, -35, -17, 34,
  -1, -28, 45, -68, 27, 70, 67, 7, 10, 7, 39, -23, -10, -17, 65, 56, -72,
  -80, -45, 37, -24, -28, 59, -14, -3, 6, 5, 64, -10, 41, -50, -25, -10, 22,
  -19, 0, 10, -51, -28, 0, -19, 37, 37, 34, -17, 115, -57, -2, 25, -7, 16,
  32, -2, 8, -4, 32, -18, 26, -10, 13, -6, 66, -2, -28, 19, -15]

theorem fractionalNearFrameSubtreeG3R0194_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0194Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0194Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0194Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0194_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0194LowerBoundTable : List ℤ :=
  [4, 2, 2, 1, 137, 3, 56, 70, 16, 99, 130, 126, -200, -10, 113, 10, 117,
  10, -112, 84, 112, 134, -15, -63, 47]

def fractionalNearFrameSubtreeG3R0194LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0194Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0194LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
