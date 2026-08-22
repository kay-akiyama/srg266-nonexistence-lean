import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0162`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0162Mask : ℕ := 1380053291549260

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0162Witness : Array ℤ :=
  #[-18, -21, 8, 51, -9, -15, 11, 9, 14, -47, 65, -7, -16, -1, -30, 64, -11,
  -3, -23, 0, -7, -13, 14, -4, -10, -39, 63, 21, 165, 35, -12, 0, -10, -29,
  51, -39, -78, 60, 47, 13, 16, -113, -4, -86, -44, -60, -41, -20, 42, 24,
  -3, 64, -2, 16, -50, -95, 22, 12, 67, -72, -2, -43, 34, -6, -28, -20, 57,
  -20, 21, 31, 31, 68, -5, -5, 24, 47, 26, -32, 16, 15, 8, -19, 7, 18, -88,
  30, 62, 22, -35, -83, 0, 10, 22, -18, 88, -86, -7, -3, 3, 27, -26, 38,
  -20, 17, 2, -122, 50, 9, -26, 46, -5, -47, -23, -17, 0, 68, -74, 15, 17,
  -25, 4, 9, -36, 15, 23, -35, 3, -14, 4, -46, 16, -55, -58, 56, 10, 19, 96,
  87, -5, 49, 3, -19, 60, -6, 28, 14, 131, -76, 30, 31, -10, -9, -9, 114,
  -54, -58, -48, -14, 18, 50, -4, -41, -86, 88, 43, -133, 40, 15]

theorem fractionalNearFrameSubtreeG2R0162_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0162Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0162Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0162Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0162_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0162LowerBoundTable : List ℤ :=
  [-46, 33, -92, 104, 1, -80, -28, 2, 2, 10, 222, 102, 41, -13, 10, 72, -84,
  165, 63, 180, 283, 8, 29, 10, 48]

def fractionalNearFrameSubtreeG2R0162LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0162Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0162LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
