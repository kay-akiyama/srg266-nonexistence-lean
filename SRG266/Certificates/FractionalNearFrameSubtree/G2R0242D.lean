import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0242`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0242Mask : ℕ := 5161765677154892

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0242Witness : Array ℤ :=
  #[-37, -41, -42, -28, -62, -33, 9, 30, -21, -73, -90, 23, 71, 144, 109,
  83, 8, 2, 42, 44, 23, 57, 34, 54, -30, 21, -61, -119, -33, -123, -51, -1,
  48, 38, 53, 49, -76, -92, -4, 32, 182, 73, -39, -110, 38, -58, 36, 16, 21,
  5, 20, 21, 132, 26, -59, 39, -24, 18, -39, -62, 40, -12, -27, -43, 9, -9,
  -25, -22, 52, -13, 13, -15, 33, 10, 42, 16, 39, 41, 14, -48, 39, -31, -43,
  -21, 4, -6, 1, -68, 61, 6, 44, -24, -88, -5, -59, -21, -5, -11, 71, 53,
  -7, -34, 15, -37, 2, -5, 0, -88, -56, 66, -1, 57, 26, -52, 16, -60, 28,
  -33, -93, 36, -53, 36, -44, 35, 4, -30, -9, -29, -53, -11, 12, -70, -17,
  -63, 24, 55, 130, 51, -178, -25, 40, 59, -99, 83, -63, 69, 23, 1, 2, -1,
  -115, -25, 79, 30, 17, 21, -17, -23, -7, -53, 14, 11, -1, 41, 9, -59, -7,
  -50]

theorem fractionalNearFrameSubtreeG2R0242_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0242Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0242Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0242Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0242_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0242LowerBoundTable : List ℤ :=
  [-86, -76, 2, 1, -14, 2, -88, 12, 2, -113, -236, -58, 140, 105, -17, 116,
  -226, -19, 10, 28, 30, 141, 11, 43, 128]

def fractionalNearFrameSubtreeG2R0242LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0242Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0242LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
