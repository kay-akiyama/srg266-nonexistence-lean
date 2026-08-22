import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G4R0041`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0041Mask : ℕ := 5471808498663778

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0041Witness : Array ℤ :=
  #[-85, -43, 53, 0, 24, 147, -56, -91, -19, -37, 125, 0, 45, -75, -62, 1,
  17, -95, 48, -25, -8, 24, -32, -28, 56, -16, -35, -43, -73, 35, -70, 104,
  0, 19, 71, -48, -52, 99, 22, 16, -56, -42, -58, -88, 47, 75, -73, -61,
  -13, -3, -45, 24, -102, -87, 11, 171, 173, 38, 17, 6, 49, 11, -22, -19,
  -35, 0, 34, 30, -1, 58, 63, -42, -35, -89, -9, 51, 16, 24, -15, 40, -101,
  -7, 4, 65, 12, 2, 58, 49, 89, -85, -137, 14, 2, 4, 43, 72, 74, -133, -47,
  -63, 7, -101, -87, -20, -82, 92, -31, 9, -66, -3, 45, 44, 22, -39, -31,
  -20, -20, -38, 0, 96, 38, -50, 55, 37, 24, -72, 15, 17, 91, -58, 141, 59,
  -26, -48, -115, -24, -19, 91, 133, -27, -15, 35, -2, 114, -21, 56, -74,
  -63, -22, -15, 54, 4, -16, 43, -7, -7, 97, 140, 128, 74, 86, 108, 112,
  125, 48, 82, -66, 23]

theorem fractionalNearFrameSubtreeG4R0041_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0041Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0041Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0041Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0041_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0041LowerBoundTable : List ℤ :=
  [-61, 264, 27, 0, 1, 59, 137, -149, 2, 431, 363, 154, -8, -102, 354, -46,
  653, 3, 204, 11, -319, 126, 367, 46, -63]

def fractionalNearFrameSubtreeG4R0041LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0041Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0041LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
