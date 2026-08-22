import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0417`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0417Mask : ℕ := 5748885554438504

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0417Witness : Array ℤ :=
  #[93, 87, -81, -43, 78, -94, -61, -87, -81, -58, 57, -75, 111, 78, 117,
  19, 202, 46, -30, -125, -34, 66, -59, -76, -20, -72, -22, 12, 54, -44, 18,
  79, 0, -81, -65, -31, -28, -55, 48, -150, 7, -124, -21, 8, 50, 0, -10,
  -88, -45, -83, 3, -33, -93, -99, 14, 81, 28, 119, 95, -85, 12, 41, -39,
  33, -75, -190, -73, 100, -53, -40, 37, -40, 21, -40, -129, -78, -2, -20,
  143, 60, 19, 36, -38, 95, -34, 34, 120, -128, 141, -76, -36, -66, 39, 121,
  71, 131, -72, -58, 46, -58, -26, 106, 91, 45, -81, 39, -12, 1, -47, -86,
  118, 1, 171, -40, -8, 96, 67, 41, 157, 115, -47, -44, 20, 43, -32, -38,
  -15, 77, 100, 50, 52, -59, 39, 103, -94, 14, 35, 33, 6, 127, 90, 116, 53,
  105, -23, 61, 99, 143, 59, -35, 107, -258, -26, 134, 39, -85, -29, 79, 23,
  107, 57, 29, 127, -98, 77, 75, 63, 140]

theorem fractionalNearFrameSubtreeG2R0417_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0417Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0417Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0417Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0417_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0417LowerBoundTable : List ℤ :=
  [66, 479, 191, 192, 61, 2, 16, -129, 36, 372, 548, 90, 343, 94, 109, 185,
  31, -4, 333, 435, 208, -145, -25, 55, 11]

def fractionalNearFrameSubtreeG2R0417LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0417Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0417LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
