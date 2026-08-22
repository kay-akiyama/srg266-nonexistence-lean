import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0418`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0418Mask : ℕ := 5748902725395048

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0418Witness : Array ℤ :=
  #[-21, -2, -12, 1, -20, 50, -12, -43, -2, -55, -2, -13, 12, 4, -21, 18,
  -43, 37, 7, 90, -11, -5, 48, 87, 1, -14, -40, -67, -10, -27, -97, -10,
  -89, 10, 77, 96, 45, -30, 19, -38, 51, 66, 43, -9, 16, -37, 30, 19, -37,
  -43, 47, 7, 46, -21, 6, -24, -57, 2, -45, 74, 50, -9, -26, 0, 56, -35,
  -57, 43, 0, -43, -69, 14, 54, 18, 11, -48, 3, 18, 47, 24, -29, -12, -33,
  55, -19, 19, 46, 50, 80, -24, 18, 45, 1, -33, 34, 26, -65, -4, 62, 27, 80,
  0, -3, -31, -3, 61, 12, 30, 7, -45, -55, -32, -5, -25, 0, 16, -132, -104,
  23, 41, 57, 11, 7, 104, -28, -9, -52, -32, 30, -35, -33, -102, -45, -36,
  -7, -23, 34, 1, 18, -51, 14, -19, 1, 13, -80, -23, -2, 23, 20, 51, -45,
  44, 15, 78, 51, -65, 11, 40, -5, 60, -6, 24, -31, 17, 20, -22, 18, 10]

theorem fractionalNearFrameSubtreeG2R0418_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0418Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0418Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0418Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0418_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0418LowerBoundTable : List ℤ :=
  [-42, -51, 3, 26, 2, -37, 36, 16, -27, 73, -165, 242, -155, 163, 113, 79,
  203, 165, 9, 11, 10, 152, -40, 100, 87]

def fractionalNearFrameSubtreeG2R0418LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0418Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0418LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
