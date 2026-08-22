import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0450`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0450Mask : ℕ := 5793165325079330

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0450Witness : Array ℤ :=
  #[-34, -196, 91, -46, 209, 136, -402, -237, -137, -119, -5, -17, -39, 221,
  114, 330, 130, 15, -43, -23, 49, 20, 93, 50, -71, -87, -2, 134, -71, -15,
  160, -27, 56, -27, 181, -43, 0, 136, -78, 44, 15, -203, -86, 123, -4, 14,
  -30, -75, 243, 95, -103, -74, -165, 63, 97, 303, 78, 26, -131, -82, 49,
  108, -40, -30, -61, 26, 28, 296, 64, 22, -63, 66, 31, -108, -4, 121, 33,
  44, -123, -23, -60, -31, 30, 17, 33, 52, -8, 64, 10, -2, -33, -161, 47,
  142, -95, -30, -2, -25, 34, 44, 148, -46, 130, 38, -51, 53, 37, -102, 93,
  13, -16, 109, 11, 169, 83, 120, 84, 13, 62, 66, 201, -184, -34, 85, -119,
  11, 41, 91, -99, 9, 14, -73, 7, -114, 287, 27, 17, -29, 77, 26, 57, 0, 69,
  91, 168, 19, 83, -1, 31, 194, -50, -26, 92, -136, 11, -48, 227, -64, 78,
  -48, 154, -41, -55, 64, -103, -105, 25, -175]

theorem fractionalNearFrameSubtreeG2R0450_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0450Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0450Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0450Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0450_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0450LowerBoundTable : List ℤ :=
  [81, 216, 190, 152, 311, 315, 81, 1, 2, 533, 392, 237, 505, 10, 35, -252,
  848, -265, 507, 807, 11, 406, 296, 44, 398]

def fractionalNearFrameSubtreeG2R0450LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0450Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0450LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
