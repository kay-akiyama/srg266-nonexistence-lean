import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0209`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0209Mask : ℕ := 2361440028574211

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0209Witness : Array ℤ :=
  #[-47, 85, -42, 0, -83, 37, 59, -18, 4, 9, -27, 10, 0, 69, 18, 117, 33,
  58, -78, -2, -81, 6, -53, 71, 48, -21, 108, -7, 100, -48, 0, -5, -7, -131,
  -5, 162, 77, 100, 39, -164, -39, -27, 5, 1, -26, 138, -86, -11, -25, -34,
  87, -31, -20, 43, 61, -14, 11, -43, -39, -42, 25, -46, 7, -48, 33, -4, 8,
  34, -74, -22, -4, 28, -13, 55, -14, 21, -6, 3, 11, -27, 31, -35, -22, 16,
  -35, -16, 19, 3, -51, -4, 58, -47, 59, 63, 41, 62, -5, -22, 21, -25, 23,
  13, -81, 11, -77, 58, -36, 14, 96, -17, -23, 16, 48, -10, -33, 150, -10,
  8, -5, 134, 82, -34, 107, 93, -29, -7, 68, -51, 49, -66, -47, 32, 25, 75,
  -20, 48, -9, 6, 1, -76, -24, -4, -8, 92, 5, 14, -1, 82, 73, 56, 40, -12,
  -17, -32, 64, 96, -1, -31, 9, 22, -12, 46, 63, -24, 9, -1, -9, -123]

theorem fractionalNearFrameSubtreeG2R0209_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0209Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0209Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0209Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0209_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0209LowerBoundTable : List ℤ :=
  [64, 189, 2, 2, 126, 130, 16, 195, 4, 308, 290, 166, 10, 59, 3, -43, 35,
  -10, 141, 215, -175, 112, 484, 9, 259]

def fractionalNearFrameSubtreeG2R0209LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0209Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0209LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
