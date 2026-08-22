import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0035`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0035Mask : ℕ := 954155147362514

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0035Witness : Array ℤ :=
  #[52, 71, 45, -16, 66, 22, -29, -38, -52, -27, 75, -20, -3, -5, 37, 0,
  -28, 121, 34, 30, 79, -41, -3, 30, -44, -76, 18, 61, 94, -26, 5, 7, -43,
  -35, -3, -104, -50, 48, 33, -41, 50, -102, 45, 148, 0, 58, 33, -12, 26,
  23, -6, 53, -106, -41, -35, -54, -124, -22, 28, 16, -1, 23, -5, -5, -93,
  -2, 7, 13, 11, -5, -13, 22, -56, 32, 7, -37, 24, -11, -18, 90, 17, -23,
  -6, -26, 24, 67, -1, 19, 17, 32, -22, 7, -76, -12, -5, 9, 39, -32, 44, 19,
  91, 6, 46, 76, 46, 44, -17, 22, -141, 41, 51, -3, 14, -5, 26, 4, -66, -31,
  39, 59, 31, -10, 31, 45, -30, 50, -49, -32, -50, 94, 24, -7, -24, 52,
  -116, 98, 76, 143, 55, -89, 60, 91, 29, 20, 42, 49, 101, 28, 16, -2, 49,
  20, -114, 13, 147, -3, 2, -33, 22, -36, -60, -65, -49, -80, -72, -50, 75,
  59]

theorem fractionalNearFrameSubtreeG3R0035_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0035Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0035Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0035Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0035_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0035LowerBoundTable : List ℤ :=
  [16, 96, -66, 145, 144, 3, 103, 72, 0, 193, 254, 201, -2, -105, 489, -139,
  -42, -3, 372, 113, 158, 206, 331, 10, 88]

def fractionalNearFrameSubtreeG3R0035LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0035Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0035LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
