import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0075`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0075Mask : ℕ := 965942183563504

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0075Witness : Array ℤ :=
  #[46, 96, -25, -4, 28, 33, 17, -20, -32, -112, 7, 113, 63, 11, 34, 14, 7,
  -8, -59, 48, 71, 3, -60, -37, 79, 41, 39, 39, -16, 52, 77, -15, -44, 34,
  43, 12, -108, -126, -45, 10, 29, 0, -36, 132, -62, 14, 85, -60, 34, 15,
  40, 70, -50, -111, -33, -103, 19, 0, 5, 9, 51, 18, -6, 2, 56, -65, 14, 62,
  -11, 24, 92, 1, 34, -4, 126, 45, 34, -22, 97, -74, 61, -30, 26, 2, -66,
  49, 5, 4, -1, -116, -47, -16, -80, 51, 57, -25, 116, 40, -3, 32, 44, 96,
  13, -26, 13, -76, 47, -35, -93, 86, -9, 0, 10, -53, -11, -23, -7, 59, -13,
  99, -96, -46, 16, -71, -13, 19, -8, -6, 28, -1, 16, 25, 31, -10, -7, 21,
  15, 22, 101, -48, 2, -87, 63, 39, 0, 93, -18, 49, 89, 90, 52, 46, -17,
  112, -2, 9, -127, 22, -41, 35, -43, -34, -101, 75, -27, 34, 15, 83]

theorem fractionalNearFrameSubtreeG2R0075_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0075Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0075Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0075Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0075_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0075LowerBoundTable : List ℤ :=
  [43, 98, -47, 104, 184, -17, 110, 75, 91, 10, 134, 31, 98, 6, 147, 114,
  83, 213, -17, 96, 150, 383, 474, 229, 218]

def fractionalNearFrameSubtreeG2R0075LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0075Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0075LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
