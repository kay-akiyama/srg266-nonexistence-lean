import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0060`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0060Mask : ℕ := 969062905135754

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0060Witness : Array ℤ :=
  #[-54, 16, -59, -85, 45, -16, 22, -73, -86, 43, 16, 5, 90, -47, -6, -14,
  0, 57, 88, 68, 37, 31, -105, 22, -111, -41, 24, -32, -63, -15, -33, -5,
  -51, 24, 39, 30, 72, -13, -23, 13, 77, -30, 43, 17, 43, 37, 71, -11, -66,
  -51, 2, 13, -21, -15, -68, 14, -3, 0, -1, -24, 67, -69, -8, 72, 155, -117,
  -89, 0, -37, -8, 19, 22, 0, 17, -66, 0, -44, 25, 5, -7, -16, -2, 25, 98,
  -10, -117, 7, 11, -15, -22, 3, 5, -79, -71, 17, 34, 96, -64, 73, -54, 8,
  48, -27, -44, 98, 22, -44, 40, -31, 101, 27, 88, -64, 0, -83, -44, -18,
  42, 91, 87, -11, 52, 12, -52, -17, -2, 14, 45, 59, 39, -11, -21, 21, 30,
  -46, -71, 14, 35, 75, 37, 14, 8, 47, -50, 18, -38, -86, -16, -15, 4, 24,
  22, 11, 21, -58, -17, -42, 38, 54, 55, -39, 24, 80, 94, 65, 84, -15, -20]

theorem fractionalNearFrameSubtreeG3R0060_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0060Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0060Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0060Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0060_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0060LowerBoundTable : List ℤ :=
  [-36, 141, 52, -142, 1, 130, 17, 1, 1, 119, 150, 279, 9, 168, 215, 10,
  104, 41, 149, -213, -243, -138, 87, 337, 16]

def fractionalNearFrameSubtreeG3R0060LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0060Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0060LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
