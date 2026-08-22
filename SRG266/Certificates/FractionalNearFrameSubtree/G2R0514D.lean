import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0514`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0514Mask : ℕ := 5812278052443668

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0514Witness : Array ℤ :=
  #[-40, 35, 16, 10, 37, -14, -50, -14, 32, 34, -24, -17, -64, 95, -71, 170,
  -3, -44, -73, 118, 13, 45, 33, -50, 132, 52, 15, -107, -53, 101, -3, 57,
  15, 83, -84, -76, 60, 34, 25, -36, -208, 213, 109, 32, 130, 6, 166, 22,
  -199, -130, -160, 165, 39, 173, -73, 59, -51, 195, -71, -13, 108, 133,
  -112, -73, -38, 20, -98, 65, -19, 20, -92, 48, 121, 89, 114, 40, 7, -10,
  -53, -63, -74, 13, -74, 24, -9, 7, -121, -5, 21, 7, -98, 126, 27, 8, 41,
  164, -9, 152, 51, 34, -54, -62, -54, -4, 56, 53, 43, -22, 132, -33, -55,
  -59, -41, 38, -18, -36, -9, 23, -182, -82, 63, -29, 109, 9, 4, 206, 46,
  -47, -31, -42, 36, 101, 95, 138, 41, 64, 34, -127, -21, -127, -59, -95,
  91, -36, 66, -5, -107, 120, 175, 32, 8, 84, 131, -36, -1, 48, -183, -25,
  139, -153, 77, 58, 116, 111, 120, -59, -30, -44]

theorem fractionalNearFrameSubtreeG2R0514_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0514Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0514Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0514Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0514_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0514LowerBoundTable : List ℤ :=
  [74, 135, 134, 47, 4, 1, 179, 122, 113, 214, 584, 10, 251, 152, 982, 148,
  92, 308, -42, 213, 57, 362, -43, -47, 495]

def fractionalNearFrameSubtreeG2R0514LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0514Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0514LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
