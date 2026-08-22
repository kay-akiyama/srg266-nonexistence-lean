import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0327`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0327Mask : ℕ := 5390546154148528

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0327Witness : Array ℤ :=
  #[52, -16, 41, 43, 104, -100, -73, -92, -14, -66, 82, -20, 95, 47, 30, 39,
  -10, 78, 27, -10, 35, -53, 7, -21, -61, -58, -31, 37, -33, 2, 26, -10,
  -48, -7, -28, -22, 32, 47, 9, -18, -72, 87, 151, 11, -7, -100, 76, 52,
  -93, 125, 50, -35, 39, 23, 88, 0, 109, -18, 57, -4, -6, 65, -111, 44, 3,
  -4, -10, -116, 40, 68, -65, -14, -31, -68, -33, 80, 29, -28, -84, 10, 12,
  -88, 38, 31, 16, -49, -29, 11, -11, 87, 43, 110, 159, 26, 3, -51, -116,
  -182, 65, -5, -68, -55, -35, 9, -3, 57, 145, -125, 7, -41, 49, 11, 7, -44,
  68, 120, 67, -58, -39, -136, 24, -96, -64, -27, 0, 103, -39, 1, -47, -107,
  62, 155, -227, 134, -83, 93, -74, -67, 26, 30, 41, 74, 9, -9, 122, 49,
  -34, 39, -12, -14, 15, 75, 88, 64, 43, 39, -44, -47, 80, -94, -18, 120,
  51, -102, 66, 63, -103, 22]

theorem fractionalNearFrameSubtreeG2R0327_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0327Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0327Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0327Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0327_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0327LowerBoundTable : List ℤ :=
  [-25, 41, -46, 90, 77, 71, -22, 2, 2, 378, -291, 55, 87, 9, 364, -4, 195,
  88, 75, 426, 217, 80, -201, 310, 69]

def fractionalNearFrameSubtreeG2R0327LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0327Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0327LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
