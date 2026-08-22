import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0118`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0118Mask : ℕ := 5794204369754401

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0118Witness : Array ℤ :=
  #[2, -12, 9, -40, -41, 7, 8, 49, -17, -20, -20, 49, 27, -69, 54, -1, -27,
  4, -23, 27, -28, -10, -1, 34, 10, 15, 1, 2, 1, 0, -10, 15, -14, 5, 70, 59,
  -40, -74, 86, 106, 38, -84, -57, -32, -14, 7, -11, -24, 9, 18, 45, 46, 39,
  11, -5, -1, -31, -10, -15, 2, 19, -42, 14, 24, 51, 20, 44, -5, -39, 12,
  -32, 1, 15, -30, 16, 35, -28, 12, -3, 56, -5, 60, 32, 14, -5, 58, 35, 17,
  -22, 24, -42, 60, 18, 41, -1, 43, -58, 15, -21, 47, -19, -39, -1, 21, 32,
  -6, 52, -19, -2, -21, -14, 49, 13, -12, 41, 17, -34, 15, 45, -72, 7, -6,
  -2, -25, 26, 58, -55, -5, -6, 8, 27, -19, 26, 2, -35, 57, 26, 26, -15, 25,
  -55, 3, 7, -35, 31, -29, -16, -2, -65, -45, 67, -35, 44, 21, 26, 32, 30,
  6, 41, 15, -11, 13, -35, 27, -8, 0, 38, -37]

theorem fractionalNearFrameSubtreeG5R0118_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0118Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0118Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0118Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0118_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0118LowerBoundTable : List ℤ :=
  [22, 35, 139, 67, -32, 2, 76, 97, -8, 130, 108, 159, 46, 174, 100, 304,
  201, 104, 19, 10, 11, -44, 29, 19, -35]

def fractionalNearFrameSubtreeG5R0118LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0118Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0118LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
