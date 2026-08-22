import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0023`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0023Mask : ℕ := 901173665503777

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0023Witness : Array ℤ :=
  #[-77, -35, 0, 51, 33, -89, 45, 33, 28, 0, 0, -13, 43, -2, 11, 6, 4, 6,
  -93, -13, 20, 28, 9, -26, 82, 90, 27, 26, -8, -56, -48, 12, -47, -14, 47,
  27, 24, -14, -6, -21, 48, 29, 27, 36, 28, 5, -2, 67, -4, -44, 7, -14, 42,
  15, 9, 23, 50, 25, 48, 26, -15, -11, -27, -13, -26, -33, -50, 35, -1, -23,
  8, -25, 0, 14, -1, -9, 67, -56, -64, -60, -66, 68, 70, 34, 26, 14, -1, 49,
  126, -44, 31, -36, 24, -54, 0, -64, -50, 9, 14, 5, 40, -24, 1, 32, 7, -7,
  -31, -3, -43, -47, -51, -15, -40, -16, 64, 4, 15, -98, -75, -6, -6, -113,
  30, 23, -134, -102, -27, 18, -121, -14, 5, -10, -16, 24, 0, -4, -13, -15,
  8, 42, 39, 0, 13, -14, -5, 61, 19, 7, 6, 23, 93, 45, 52, -82, -28, -9,
  -45, -10, 80, -24, 10, 94, -11, 51, -15, 81, 8, -159]

theorem fractionalNearFrameSubtreeG3R0023_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0023Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0023Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0023Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0023_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0023LowerBoundTable : List ℤ :=
  [-59, 13, 51, 2, -57, 2, -77, 23, -4, 67, 35, 11, -83, 10, 164, 125, -61,
  -147, 242, -19, 108, -31, 10, -51, -31]

def fractionalNearFrameSubtreeG3R0023LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0023Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0023LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
