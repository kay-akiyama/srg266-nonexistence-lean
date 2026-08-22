import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0066`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0066Mask : ℕ := 954133976290450

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0066Witness : Array ℤ :=
  #[114, 57, 43, 56, 16, 44, 8, -139, -121, -48, -65, 51, 69, -34, 116, 0,
  55, 4, -82, -44, -64, 75, 11, 20, -45, -3, 52, -4, 30, 30, 52, -21, -5,
  73, 50, -86, -133, 111, 4, 12, -197, 6, 2, -40, 24, -21, -45, 73, 0, 49,
  21, 13, -57, -122, -72, -93, 36, 150, 12, 4, 141, 39, 55, 104, 89, 11, 42,
  -77, 25, -28, 49, 40, 50, 11, -22, 49, -28, 30, -14, 4, -75, 50, -23, 23,
  5, 59, 11, 24, 19, 15, 137, -166, 25, -13, 40, 35, -5, -38, 0, 50, 11,
  -117, 6, -5, -53, 57, -6, 52, -13, -31, 1, 102, -42, 0, -57, -52, -7, -60,
  -31, -42, 192, 22, 61, 12, 25, -69, 10, -5, 67, 66, -97, 91, -89, 142, 75,
  56, 18, -9, 0, -11, 48, -58, 5, -12, -5, 200, -96, 25, -70, 172, -138, 35,
  9, -132, 87, 22, -27, 21, 19, 0, 36, -24, -58, 79, 15, -207, 83, 60]

theorem fractionalNearFrameSubtreeG2R0066_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0066Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0066Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0066Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0066_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0066LowerBoundTable : List ℤ :=
  [18, 69, 1, 88, -51, 117, 117, 162, 127, -56, 143, 190, 9, 96, 216, 209,
  212, 126, 10, 188, -225, -83, 79, 236, 235]

def fractionalNearFrameSubtreeG2R0066LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0066Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0066LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
