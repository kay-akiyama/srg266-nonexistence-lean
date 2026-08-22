import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0392`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0392Mask : ℕ := 5739960494965514

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0392Witness : Array ℤ :=
  #[-37, 56, 37, 77, 97, -32, 0, -23, 9, 15, 28, -65, -39, 16, -25, -111,
  -7, -24, -28, 59, -24, 8, -46, 15, -58, -2, 5, -82, 0, 60, -43, -89, -33,
  -97, 53, 7, 56, 71, -4, -26, -97, 88, -72, 7, 12, 17, -31, 14, 12, -58,
  -10, 27, -25, -14, -6, -151, -8, -10, 23, 65, 24, -68, 21, 43, 79, 40, -3,
  25, -31, -112, -24, 58, 72, -136, -15, 8, 3, -112, 47, -1, -78, 43, -53,
  -43, 37, 31, 29, -50, -15, -72, -4, -136, 49, -35, -49, 43, -3, -17, 33,
  8, 5, 27, 27, 78, 26, -2, 36, 8, 38, -13, -62, 33, -53, -145, -60, -88,
  -39, 73, -4, -73, 137, -17, 27, 31, -13, 38, -28, 61, -30, -21, 63, 66,
  42, 107, 9, 87, -20, -44, -2, 10, -46, 11, 4, -28, -37, -85, 29, 10, 62,
  -33, 3, 8, 109, 18, -88, -99, 71, -13, -119, 91, 78, 8, 62, 87, 39, 33, 8,
  62]

theorem fractionalNearFrameSubtreeG2R0392_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0392Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0392Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0392Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0392_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0392LowerBoundTable : List ℤ :=
  [-133, 69, -20, 2, -182, 33, -23, -19, -197, 83, 192, 216, -130, -17, 10,
  -125, 119, 9, 75, 226, 198, 28, 10, -19, 10]

def fractionalNearFrameSubtreeG2R0392LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0392Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0392LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
