import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0517`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0517Mask : ℕ := 5815957911213144

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0517Witness : Array ℤ :=
  #[9, -20, 59, -59, -30, -19, 54, -7, -48, -64, -63, 53, 24, -22, -19, -6,
  -46, -93, -17, 61, -35, 19, 15, 122, -69, 22, -26, 14, 36, 11, 82, -31, 0,
  0, -5, -69, 13, 98, 8, 15, -45, -10, 48, -59, 28, 51, -27, -2, -84, -34,
  13, 43, 84, 6, 14, 63, -37, -52, 45, -91, 98, 1, 31, -84, -23, -6, -58,
  -20, 45, 40, -100, 39, 4, 37, 36, 42, -72, -57, 36, -18, 37, 54, -82,
  -123, 131, -52, -23, 34, 50, 81, -16, 44, -2, 34, 14, -18, -6, 41, -28,
  11, 7, -51, 91, -22, 20, -101, 73, 41, 110, -8, 0, -61, 47, 52, 52, 86,
  -87, -44, 2, -21, 64, 35, 70, 5, -113, -43, 50, -83, 69, 120, 36, 1, -76,
  -8, -9, 18, 41, 68, 50, 9, -26, -43, -23, 92, -42, 22, 62, -174, -18, 16,
  -78, 0, -56, 61, -66, 65, 40, -5, 107, 9, -24, -46, -19, -15, -8, 93, 6,
  -19]

theorem fractionalNearFrameSubtreeG2R0517_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0517Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0517Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0517Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0517_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0517LowerBoundTable : List ℤ :=
  [-47, 67, 71, 51, -12, 1, 14, 1, -73, 97, 138, -124, -112, 195, -3, 410,
  11, 10, 11, 359, 127, 52, 265, -34, 17]

def fractionalNearFrameSubtreeG2R0517LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0517Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0517LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
