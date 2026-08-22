import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0346`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0346Mask : ℕ := 5668890727880977

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0346Witness : Array ℤ :=
  #[-52, -58, -33, 0, -1, 16, 26, -73, 13, 66, 0, -54, 44, -18, 114, -58,
  40, -32, -88, 36, -27, 6, -8, -11, 46, -5, 104, -14, -5, -17, -85, 52,
  -103, -93, -73, -41, 102, 27, 18, 0, 51, -12, 61, 23, 38, 100, -11, -13,
  0, -1, 105, 15, -46, -30, 27, 44, 1, 1, -25, 30, -4, -76, 1, 67, 21, -22,
  3, 19, -18, 38, -8, -20, -6, 78, 50, 65, 76, 11, 8, 2, -38, 45, -68, -24,
  10, 22, 113, 11, 25, -19, 121, 70, 24, -35, -39, -23, -38, 49, 14, 48,
  -24, -2, -5, -6, -2, 66, 19, 11, -13, -15, 10, -3, -148, 69, -101, 11,
  -42, -12, -18, 103, -14, -56, 15, -26, 18, -33, 68, -34, 30, -50, 7, -33,
  -39, 41, 35, -40, 14, 31, 45, -73, 34, 1, -32, 17, -74, 110, 27, 118, -18,
  77, 93, -3, 85, 42, 27, 12, -37, -5, -44, -19, -37, -51, -29, -23, 105,
  33, 5, -6]

theorem fractionalNearFrameSubtreeG2R0346_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0346Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0346Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0346Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0346_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0346LowerBoundTable : List ℤ :=
  [-27, 30, 35, 93, 134, 1, 3, 56, 2, 148, 203, 216, 71, 163, 40, 130, -120,
  117, 3, -152, 375, 79, 212, 170, 233]

def fractionalNearFrameSubtreeG2R0346LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0346Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0346LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
