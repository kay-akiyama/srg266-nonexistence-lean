import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0358`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0358Mask : ℕ := 5707406643930374

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0358Witness : Array ℤ :=
  #[-4, -22, -17, -25, -40, -34, 33, 9, 10, -2, 25, 8, 21, 13, -8, 42, 51,
  3, -25, -22, 0, 24, 18, -11, -25, 6, -5, -18, 7, 0, 4, 18, -13, 3, -10,
  38, 35, 31, -24, -3, -17, -16, -5, -25, -37, -26, -9, 25, -6, 12, 7, 1,
  -21, -36, 7, 31, 11, -6, -9, -27, -12, 6, 58, 0, 62, -9, 33, -31, -23, 36,
  -32, -34, 68, -18, 6, -11, -12, 1, 4, -40, -27, 2, 27, 5, 49, -21, -27,
  22, -17, 34, -12, -5, -23, 12, -33, 30, 19, 21, 21, -36, 41, 13, -26, -22,
  65, -22, 53, 41, -12, -25, 0, -12, -10, 11, -35, 1, -45, -2, -20, -5, 30,
  -13, 15, 24, -13, -6, -17, 29, -12, 19, -20, 3, -21, -24, 15, 26, 0, 4, 5,
  4, -21, 14, 13, -34, 16, -11, -5, 9, -11, 55, -28, 33, -39, -42, 42, 20,
  -15, -4, -43, 17, -28, -5, -6, -5, 14, -8, 8, -18]

theorem fractionalNearFrameSubtreeG2R0358_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0358Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0358Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0358Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0358_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0358LowerBoundTable : List ℤ :=
  [-40, -45, -54, 6, 34, 46, 38, 16, 3, -76, 147, -50, 72, 10, 143, 65,
  -171, 8, 22, -39, -53, 9, 106, 9, -26]

def fractionalNearFrameSubtreeG2R0358LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0358Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0358LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
