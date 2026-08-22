import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0201`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0201Mask : ℕ := 2343985533654019

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0201Witness : Array ℤ :=
  #[-32, 80, 20, 188, -101, 308, -46, -19, 81, 0, -120, 17, 63, -203, 88,
  98, 43, 0, -64, -12, -10, 141, 15, 307, -29, 163, -49, -14, 85, 56, 59,
  149, 155, -401, 53, -21, -125, -124, 116, 211, 225, 46, 25, -179, 53, -76,
  453, 119, 126, 174, -24, -85, -108, 222, 121, 61, 42, -132, -180, 84, 66,
  120, 24, 35, -85, 175, 39, -149, 19, -29, 3, 0, 152, -24, 144, -135, 70,
  7, 17, -78, 36, -139, -100, 46, -122, 5, 44, -109, 5, -101, 5, 69, 62,
  -50, -11, 161, 4, -143, 22, -226, 29, -37, -57, 66, -131, -212, -79, 17,
  36, -87, -6, 2, 78, 184, 35, 262, 64, -105, 203, 77, 77, 61, -3, -65, 35,
  -36, 39, 85, 122, -74, 53, 28, -4, -18, 164, -113, -140, -21, 167, -124,
  107, 86, -33, 356, 128, -19, -11, 31, 86, 213, 4, -64, -82, 448, -59,
  -255, -129, -114, 52, 16, 26, -106, -14, 95, -23, -25, 325, -483]

theorem fractionalNearFrameSubtreeG2R0201_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0201Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0201Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0201Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0201_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0201LowerBoundTable : List ℤ :=
  [157, 292, -106, 119, 2, 176, 307, 375, 378, 970, 416, 199, 391, -410,
  -16, 11, 576, -174, 345, 62, 725, 279, 276, 487, 130]

def fractionalNearFrameSubtreeG2R0201LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0201Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0201LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
