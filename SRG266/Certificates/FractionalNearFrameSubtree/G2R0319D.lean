import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0319`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0319Mask : ℕ := 5389552214153648

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0319Witness : Array ℤ :=
  #[150, 68, 66, -10, 16, 64, -40, 87, 3, -159, -17, -33, -87, -126, 33, 18,
  25, -122, -48, 23, 28, -13, -4, -1, 141, -25, 70, 19, 4, 89, 91, -51, -18,
  15, 11, -2, -45, -90, -100, -64, 81, 88, -113, -105, -99, 81, 220, 45,
  -158, -131, -43, -207, -106, 116, 161, 58, 18, 75, -94, -35, 19, 27, 11,
  -17, -72, 276, 28, 49, -51, 7, -128, 196, 175, -87, -61, 177, 10, 242, 81,
  1, 31, 26, -30, 1, 10, 65, 145, 29, 57, 8, -29, 31, -23, -69, 117, -192,
  58, -129, 186, 2, 69, 52, 40, -33, 110, 72, 46, -39, -46, -94, -86, -11,
  -33, -62, 89, 13, 105, 33, -130, -46, -101, 189, -104, -83, 11, -83, -3,
  75, 0, 79, -94, 10, 77, 85, 108, 141, -29, 33, -50, -90, -3, 48, 82, 9,
  86, 61, 114, 125, -35, 5, 113, -26, 101, -56, 125, 36, -34, -24, 119, -76,
  -14, -51, 2, 81, 68, 30, 188, 130]

theorem fractionalNearFrameSubtreeG2R0319_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0319Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0319Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0319Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0319_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0319LowerBoundTable : List ℤ :=
  [95, 266, 349, 548, -35, -235, 196, 85, 177, 10, 792, 10, -133, 44, 235,
  154, 164, 101, 269, 410, 344, 206, 214, 303, 10]

def fractionalNearFrameSubtreeG2R0319LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0319Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0319LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
