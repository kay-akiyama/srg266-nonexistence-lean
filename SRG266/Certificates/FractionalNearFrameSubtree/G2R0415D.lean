import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0415`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0415Mask : ℕ := 5748614826677400

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0415Witness : Array ℤ :=
  #[-21, 0, 25, 44, -59, 1, -3, 30, 8, 0, 56, 51, -41, -16, 37, 39, 98, 94,
  74, -32, -2, 9, -5, 20, -57, -84, -49, -75, 12, -10, -61, 32, -5, 120, 69,
  -57, -115, -61, 6, 51, 36, -17, 5, 57, 13, 31, 41, -19, -45, 12, -51, 14,
  147, 63, -53, -42, 36, -5, 1, 38, -36, 17, -72, 50, 64, 7, 8, 53, 28, 3,
  -27, -8, 13, 19, -51, 0, 19, 3, -10, 2, 6, 33, -33, -10, -14, 26, -1, -30,
  -4, -96, -14, 14, 33, -55, 0, 60, 62, 56, 20, 43, 80, -7, 8, -18, 42, -67,
  46, 12, 40, 0, -26, 39, -19, -28, -32, 3, 58, -43, 4, -37, -4, 39, 8, -20,
  8, 74, 65, -52, -7, 42, 37, 32, 36, 47, -39, 28, -27, -20, 0, -30, 0, 22,
  -7, -45, -20, 34, 8, 70, 51, -76, -38, -60, -27, 14, 37, 15, 101, 27, 72,
  -53, -53, -23, 99, 77, 96, 104, -32, -19]

theorem fractionalNearFrameSubtreeG2R0415_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0415Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0415Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0415Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0415_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0415LowerBoundTable : List ℤ :=
  [0, 108, 78, 78, -28, 117, 106, 45, 4, 324, 67, -94, 75, 122, 160, -8,
  133, 91, 439, 233, 301, 154, 116, 191, 10]

def fractionalNearFrameSubtreeG2R0415LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0415Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0415LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
