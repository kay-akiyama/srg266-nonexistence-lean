import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0018`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0018Mask : ℕ := 677078719512657

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0018Witness : Array ℤ :=
  #[97, 0, 15, -43, 46, 18, -57, -11, -24, -137, -139, -139, 53, 141, 66,
  48, 64, 91, 79, 121, -79, 3, -38, -28, 38, -48, 78, -117, 141, -27, 32,
  -55, -48, -81, -159, 53, -28, 1, 204, 248, 125, -28, -157, -119, -144,
  290, 99, -7, 40, 81, 50, 9, -31, -27, 64, -14, -60, 3, -85, 50, 44, 75, 9,
  15, 27, -28, 148, 3, 76, -61, 75, 64, 4, -81, 36, -49, -3, 123, 36, 36,
  -21, -28, 8, 31, 127, -81, 64, -8, -43, -23, -37, 13, 75, -40, -28, 15,
  -45, -13, 22, 26, 2, 4, -22, 31, -60, -5, 75, -21, -58, -61, -55, -55, 12,
  10, 37, 31, 12, 135, -23, -41, -7, -6, 56, -26, 45, -139, -18, 17, 18, 45,
  -66, -13, -4, 40, -25, 17, -84, 24, 4, 34, 32, 12, -5, -30, 22, 18, 47,
  26, -32, 129, 57, 23, 34, -15, 4, -105, -134, 21, -47, 9, -12, -85, 32,
  111, -3, -38, 11, 0]

theorem fractionalNearFrameSubtreeG2R0018_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0018Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0018Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0018Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0018_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0018LowerBoundTable : List ℤ :=
  [-24, 1, -20, 2, -95, 130, 144, 199, 214, 95, -51, 91, -78, -54, 323, 96,
  185, -15, -3, 234, 11, 9, -67, 531, 322]

def fractionalNearFrameSubtreeG2R0018LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0018Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0018LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
