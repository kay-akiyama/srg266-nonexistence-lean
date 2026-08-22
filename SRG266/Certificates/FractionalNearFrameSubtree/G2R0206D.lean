import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0206`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0206Mask : ℕ := 2355793740927073

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0206Witness : Array ℤ :=
  #[46, 29, -5, 6, 0, 158, -39, -73, 11, 24, 17, 28, 24, -1, 10, 0, -58, 30,
  -111, 30, 148, -46, -52, 88, -8, -50, 77, 18, 55, 50, 6, 197, -58, -68,
  -183, -7, 65, 112, 48, 196, 111, 34, -37, 0, -29, 181, -91, 47, -25, 41,
  136, 55, -90, -87, 68, 3, -101, -123, 12, 65, 95, -81, 23, 0, -38, -54, 2,
  -3, 15, 72, -8, -79, -78, 120, 58, 30, -9, 47, 211, 107, 44, -53, -75, 8,
  -41, 112, 44, -21, -95, -7, -20, -6, 86, -7, 63, 56, 31, -76, -23, 18, 17,
  50, 8, -52, 2, 23, -20, 10, -14, 23, -46, 24, 54, -20, 45, 107, -35, 138,
  74, -2, -5, -73, -169, -88, 70, 82, -21, 63, -16, -25, 67, 28, 105, -30,
  -72, 132, -37, 119, -173, -14, 39, -37, 73, -59, -86, 25, -33, 72, 1, 16,
  -26, 39, 54, -28, 97, 54, -67, 67, 14, 24, -46, -25, 72, 31, 68, -1, 40,
  -124]

theorem fractionalNearFrameSubtreeG2R0206_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0206Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0206Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0206Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0206_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0206LowerBoundTable : List ℤ :=
  [31, 1, 70, 102, 227, 151, 156, 221, 84, 146, 402, 502, 23, 9, -232, -195,
  316, 519, 181, 320, 234, 284, -37, 400, 12]

def fractionalNearFrameSubtreeG2R0206LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0206Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0206LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
