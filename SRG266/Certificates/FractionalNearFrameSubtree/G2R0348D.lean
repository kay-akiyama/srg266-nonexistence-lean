import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0348`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0348Mask : ℕ := 5668906363769105

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0348Witness : Array ℤ :=
  #[-28, -90, 8, -93, -49, -68, 10, 35, 70, -37, 93, 26, 0, 50, 4, 111, 22,
  -16, 38, -1, 37, 66, 68, -63, 37, 10, -118, -15, -6, 0, -7, -24, -32, -39,
  21, -68, -6, 71, 10, 36, 50, -5, -14, -39, -84, 1, 78, 10, 25, 42, -23,
  61, -9, -11, -27, 11, -18, -3, 79, -13, 21, 7, -34, 72, 44, 37, -47, 26,
  57, -4, 20, 43, -48, 38, -19, 29, -36, -21, -9, 43, -4, 14, 16, -2, 2, -6,
  1, 32, 24, -31, 0, 5, -20, -45, -7, 10, -58, 17, 51, 68, -18, -26, -6, 24,
  -8, 42, -17, -13, -46, -16, 4, 6, -18, 12, -2, 93, 24, 43, -64, -45, 45,
  26, -82, 10, -141, 71, 59, 35, -33, 0, -57, 1, -22, 0, -8, 61, -35, -43,
  -61, 4, 98, 94, 40, 104, 64, -7, -5, -35, 47, 25, -32, 9, 4, 8, 49, -51,
  0, -5, -19, 1, -24, -20, -10, -24, -28, 50, -10, 39]

theorem fractionalNearFrameSubtreeG2R0348_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0348Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0348Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0348Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0348_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0348LowerBoundTable : List ℤ :=
  [-16, 56, 1, 2, 2, 60, 0, 58, 130, 131, 209, 80, 20, -189, 23, 28, 128,
  61, 88, 38, 141, -47, 272, 98, 105]

def fractionalNearFrameSubtreeG2R0348LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0348Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0348LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
