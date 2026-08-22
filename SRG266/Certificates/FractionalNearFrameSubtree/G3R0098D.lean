import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0098`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0098Mask : ℕ := 2518136275255954

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0098Witness : Array ℤ :=
  #[-38, 21, -25, -53, -22, 46, 11, 28, 0, 29, 15, 11, 26, 23, -16, -12,
  -37, 35, -45, -36, 57, 22, 40, -8, -9, 3, 24, -27, -28, 24, 5, -33, -27,
  15, -28, 20, 17, 2, -30, 10, 17, 25, 89, 6, -4, 36, 2, -1, -35, -39, 30,
  -14, -45, -16, -22, 1, 9, -30, 0, 2, -61, -8, 18, 28, -43, 20, 26, 30, -4,
  -1, 0, -30, 21, -21, 49, 1, 19, 8, -28, 35, -39, 6, 0, 35, -6, 31, 51,
  -11, -26, 41, -37, 35, 42, 4, -34, 3, 0, 28, 3, 8, -18, 6, -5, -51, -35,
  4, 59, 47, 26, 35, 31, 9, -21, 4, -12, -22, -75, 5, 2, 20, 31, -22, 9, 46,
  41, 14, 6, 57, -13, -14, -12, -65, 67, -53, 67, -39, 30, -20, -15, -16,
  -8, 16, 5, 29, 12, -24, 57, -27, -20, -40, -26, 19, -12, -3, 6, 39, 28,
  -24, 39, 43, -36, -35, -21, 54, 40, 0, 14, 33]

theorem fractionalNearFrameSubtreeG3R0098_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0098Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0098Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0098Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0098_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0098LowerBoundTable : List ℤ :=
  [-2, 59, 64, 44, -26, 55, 17, 6, -48, -35, 66, 166, 11, 134, 211, 11, -44,
  124, 114, 56, -121, 163, 34, 105, 163]

def fractionalNearFrameSubtreeG3R0098LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0098Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0098LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
