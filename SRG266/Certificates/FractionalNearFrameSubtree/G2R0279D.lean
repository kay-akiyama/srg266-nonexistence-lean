import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0279`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0279Mask : ℕ := 5372885324649252

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0279Witness : Array ℤ :=
  #[64, -26, 34, -28, -105, -7, -39, 94, -72, 27, 38, 17, 0, -16, 0, 81,
  103, 8, 126, 33, -21, -62, -55, 73, -64, -17, 42, -37, 0, 54, 78, 44, -41,
  -58, 14, -23, 88, 55, -79, -55, -47, 11, 26, -50, -4, 75, -49, -5, 13,
  -42, 3, 33, 17, 58, -20, -67, 40, -2, 10, 101, 28, 39, 2, -13, -73, 29,
  -83, 0, 57, 76, -54, -16, -46, -35, 68, 27, 27, -94, -61, -19, 58, -12,
  16, 62, 16, 66, 68, -99, -3, -29, -84, 43, 6, 40, 3, 2, 106, 12, 43, 39,
  -41, -11, 93, 72, -1, -33, -45, 58, -28, 6, 51, 29, -47, 23, -23, 4, -8,
  73, 37, 66, 4, -58, 139, -5, -30, -39, -52, -54, -149, -82, 70, 91, 62,
  31, -56, 45, -29, -19, 0, 45, -34, 117, 8, -16, 5, 120, -7, 0, -68, -89,
  -8, -20, 36, -40, -17, -79, 35, 26, -122, -16, 18, -33, 72, -44, 60, 40,
  -106, 46]

theorem fractionalNearFrameSubtreeG2R0279_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0279Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0279Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0279Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0279_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0279LowerBoundTable : List ℤ :=
  [15, 2, 2, 193, 2, 130, 1, 145, -58, 202, -1, -72, -121, 29, 249, 100,
  -108, -63, 428, 50, 70, -215, -16, 200, 150]

def fractionalNearFrameSubtreeG2R0279LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0279Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0279LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
