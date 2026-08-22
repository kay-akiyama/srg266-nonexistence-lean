import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0542`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0542Mask : ℕ := 6833358086180114

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0542Witness : Array ℤ :=
  #[22, 44, 78, 31, 106, 34, -138, -45, -99, -77, -110, 135, -31, 0, 81,
  109, -54, 57, -36, 7, -41, 69, 27, 79, 32, -1, -15, -27, -37, -81, -9,
  -41, -46, -90, -43, 78, 47, 73, 34, 5, -56, 52, 122, 47, -20, 32, 68, -41,
  -4, -87, 3, 23, 3, 51, -19, -87, 40, -44, 0, 31, 11, -62, 95, -79, -38,
  -4, -38, 27, 84, -28, 14, 48, -68, -19, 38, -4, -39, -69, -46, 94, -72,
  -44, -26, -20, -44, -23, -55, 47, -55, 118, -80, 0, 29, 68, 62, 9, -104,
  15, -64, 40, 12, -47, 20, -13, 67, -4, -46, -42, 17, 15, 5, -104, 42, -58,
  -18, 134, 33, 71, 84, 4, -30, -12, 68, -14, -81, -43, -65, -25, 35, -24,
  28, 66, 6, -83, -10, -48, 49, 15, -124, 39, -37, -30, 47, 15, 27, 0, -22,
  60, -7, 55, -85, 18, -73, -3, 78, -74, 48, -93, -27, -49, -39, -59, 5,
  -108, -63, -4, -7, -106]

theorem fractionalNearFrameSubtreeG2R0542_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0542Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0542Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0542Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0542_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0542LowerBoundTable : List ℤ :=
  [-103, -144, -146, -82, -10, 28, -95, 25, 2, -51, 124, -212, -141, -26,
  -212, 80, 10, -190, 195, 67, -2, 143, -121, 10, 147]

def fractionalNearFrameSubtreeG2R0542LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0542Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0542LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
