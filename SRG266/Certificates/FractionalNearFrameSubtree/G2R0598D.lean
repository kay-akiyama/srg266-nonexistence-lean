import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0598`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0598Mask : ℕ := 6868263351591280

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0598Witness : Array ℤ :=
  #[18, -3, 61, 28, -20, -16, -56, -47, -99, -11, 77, 19, 84, 42, 53, -78,
  105, -25, 18, -13, 34, 55, 24, 35, -28, 27, -16, -118, 25, 31, 86, 66, 0,
  111, -305, -114, -88, 73, 56, 186, -180, 59, 216, 54, -2, -41, -2, 17,
  117, 46, -86, -5, -140, -93, 112, 151, 219, 160, 167, -132, -174, -38, 1,
  -112, -48, 29, -90, -54, -145, -101, 70, 103, -52, 35, -80, -58, -2, -42,
  10, 41, 2, -44, 53, 24, 51, -68, 25, 11, 105, -37, -38, -44, 42, -39, -29,
  -157, 48, -44, -46, -29, 22, -22, 77, 25, 48, -91, -27, -60, 34, 14, -14,
  -13, 53, 152, -1, 82, 14, 6, 3, -6, 26, 29, 52, 30, -35, 21, 97, -75, -24,
  68, 162, -26, 94, 141, 151, -19, -36, 45, 122, 72, 28, 23, -6, -82, 59, 2,
  61, 35, 48, -75, 140, -142, -2, -4, -92, 21, 147, 17, 0, 28, -15, 32, 64,
  -113, 3, -90, 37, -29]

theorem fractionalNearFrameSubtreeG2R0598_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0598Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0598Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0598Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0598_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0598LowerBoundTable : List ℤ :=
  [23, 203, 58, -27, 153, 95, 146, 3, -40, 205, 332, 422, 92, 10, 147, 118,
  7, 114, 9, -91, 11, 241, 301, 272, 10]

def fractionalNearFrameSubtreeG2R0598LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0598Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0598LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
