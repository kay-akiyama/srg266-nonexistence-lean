import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0078`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0078Mask : ℕ := 2365523638557713

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0078Witness : Array ℤ :=
  #[-93, -102, -34, -16, -6, -75, 23, 11, 41, 0, 0, 56, -14, -19, 79, 78, 0,
  86, 56, 32, 22, 71, -47, -30, 18, 28, 4, -51, -14, 37, -37, -43, 16, 32,
  -17, 95, -51, -36, -3, -7, -34, 19, 23, -14, -1, 83, 12, -5, -4, -1, 0,
  11, -3, -36, -18, -21, -50, 68, -6, 22, 24, 1, -33, -19, 19, 0, -2, -16,
  10, 40, 92, -4, 3, 11, 11, -8, 67, 30, 143, -36, -80, 24, -13, -1, -17,
  19, -57, 32, 2, -31, 17, -81, -26, -43, -11, -11, -40, 21, -32, 1, -23,
  -37, 7, 20, -22, 69, -5, 52, 108, 30, -30, 14, 36, 68, 40, -20, 74, -13,
  -17, -44, -42, 32, 92, 64, -36, -9, 20, -15, 11, -61, 87, 104, 28, -11,
  -3, 44, -4, 68, 47, 32, 75, 9, 87, 58, 33, 50, 44, 44, 71, 95, -14, 66,
  -9, 121, 108, -54, -78, 30, 38, 6, -61, 39, 115, 6, 14, 37, 88, -42]

theorem fractionalNearFrameSubtreeG3R0078_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0078Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0078Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0078Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0078_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0078LowerBoundTable : List ℤ :=
  [97, 294, 156, 81, 245, 13, 39, 15, 95, 453, 398, 212, 307, 104, 9, 57,
  15, 126, 10, 11, 137, 302, 473, 105, 9]

def fractionalNearFrameSubtreeG3R0078LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0078Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0078LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
