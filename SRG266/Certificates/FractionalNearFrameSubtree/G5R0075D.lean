import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0075`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0075Mask : ℕ := 5332103943883096

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0075Witness : Array ℤ :=
  #[49, 64, -3, 44, 57, 39, -3, -2, 35, 49, 0, -112, -37, -35, -20, -81,
  -26, -58, -27, -46, 0, -13, -19, 19, -20, 38, 29, 37, 127, 32, 60, 10,
  -26, -27, 47, 53, -102, -5, 74, -7, -9, -36, -21, -84, 2, 6, 17, -38, 1,
  -30, -27, 25, -22, -61, 55, 9, 25, 28, -14, 22, -34, 41, 39, -58, 33, -19,
  -14, -13, -5, -13, 22, 16, -13, 15, 9, -48, 19, 20, -49, -38, -36, 59, -2,
  7, 29, 21, 43, 1, 23, -35, -24, -17, 55, 31, 9, -27, -59, 49, 60, 50, -1,
  20, -8, 14, 4, -22, 6, -12, -28, -25, 1, 8, 0, 89, -28, -1, 17, -28, 0,
  -34, -10, -8, -19, -10, 3, 4, -4, -32, -2, 71, 3, 35, 25, -28, -43, 40,
  28, -37, -3, 34, 68, 39, 7, 40, 29, 79, -33, -2, 19, -44, -12, 9, 7, 38,
  -1, 45, 26, 33, -29, 7, 27, -64, 40, -2, 30, 8, 23, 20]

theorem fractionalNearFrameSubtreeG5R0075_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0075Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0075Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0075Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0075_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0075LowerBoundTable : List ℤ :=
  [19, 100, 2, 166, 1, 101, 1, 19, 1, 3, 185, 9, 33, 142, 83, 141, 41, 82,
  96, 84, -59, 10, -11, -11, -2]

def fractionalNearFrameSubtreeG5R0075LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0075Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0075LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
