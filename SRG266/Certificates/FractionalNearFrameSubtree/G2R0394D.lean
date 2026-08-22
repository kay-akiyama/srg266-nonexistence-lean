import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0394`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0394Mask : ℕ := 5739986238817802

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0394Witness : Array ℤ :=
  #[25, 36, 13, 23, 3, 2, -122, -51, -58, -41, -57, 0, 60, 64, 28, 88, 53,
  44, 47, 52, 2, -2, 42, -40, -54, 22, -38, -95, 12, 15, -50, 3, -49, 49,
  47, 37, 16, 2, 34, 23, -11, 0, 22, -55, -21, 16, 42, 12, 13, 19, 3, 54,
  -16, -53, -72, 3, -74, -33, 100, 110, -53, -18, 34, 33, 78, -81, 35, 25,
  21, 14, 22, 13, 43, -10, 35, 50, -4, 15, 43, -37, 14, -9, -72, 42, -2, 31,
  3, 11, 2, -11, 49, -46, 29, 73, 34, 47, 33, 22, 23, 72, 59, 7, 13, -24,
  -73, -44, -48, -23, -37, 0, 46, 77, -4, -3, 17, 0, -30, -59, -8, 33, -29,
  -3, -2, 12, -28, -22, -5, -21, 31, -28, 7, -15, 51, 33, 25, -8, 36, 0, -8,
  3, 8, 19, 22, -44, 33, 1, -13, -2, -15, 38, 20, -12, 18, 3, 50, -5, 22,
  -5, -59, 27, 30, -6, 22, 3, 29, -27, -20, 1]

theorem fractionalNearFrameSubtreeG2R0394_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0394Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0394Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0394Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0394_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0394LowerBoundTable : List ℤ :=
  [30, 15, -35, 43, 143, 204, 2, -26, 111, 9, 13, 11, -60, 112, 143, 10, 93,
  110, 246, 90, 57, 89, 324, 97, 151]

def fractionalNearFrameSubtreeG2R0394LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0394Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0394LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
