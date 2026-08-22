import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0309`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0309Mask : ℕ := 5387250714666136

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0309Witness : Array ℤ :=
  #[47, -4, 38, 45, 11, -15, 1, 55, 36, -26, -44, 7, -142, 1, -23, -88, -48,
  -14, -26, -44, 68, 5, 35, -28, 27, -17, 61, 45, 139, -21, -12, 85, 0, -50,
  -111, 73, -30, 9, -46, -135, 58, -49, -51, 54, -47, -44, 25, 45, 21, 23,
  -7, 73, -30, -25, -38, 0, 35, -68, 24, 76, -25, -22, -45, 24, -150, 4,
  -55, -53, 19, 16, -15, -52, -27, 18, -20, -5, -40, 20, 35, 42, -1, 60,
  -46, -115, -43, -38, -45, 57, 41, -16, -55, -1, 1, 15, 25, -1, 14, 1, 44,
  1, -37, -62, 66, -56, -36, -64, 75, 61, 106, 3, -7, 56, 78, -21, -26, -53,
  -7, 49, 122, 86, 92, 46, 76, -3, -137, -64, 0, -104, 23, -89, 41, 38, -60,
  140, -7, -25, -2, -59, 77, 119, -17, 77, -73, 43, -15, 85, 31, 17, 93,
  102, 50, -44, 20, 67, -76, -1, 18, 48, 102, -112, -46, -43, 30, -11, 99,
  64, 0, -96]

theorem fractionalNearFrameSubtreeG2R0309_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0309Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0309Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0309Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0309_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0309LowerBoundTable : List ℤ :=
  [-71, 176, -102, -8, 75, 3, -84, 28, 69, 250, 144, 155, 94, 135, -41, -17,
  166, 292, -59, 58, -93, -169, 78, -48, 78]

def fractionalNearFrameSubtreeG2R0309LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0309Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0309LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
