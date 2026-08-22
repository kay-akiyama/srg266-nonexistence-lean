import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0023`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0023Mask : ℕ := 450642616890373

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0023Witness : Array ℤ :=
  #[0, 244, 10, -1, 19, -69, -82, 199, -42, -62, 0, -102, 100, -45, -30,
  -144, -40, -81, -122, 95, 235, -134, -263, -135, 27, 175, -184, -257, 260,
  104, 230, 201, 71, 290, 85, 26, -207, -103, -157, -38, 62, -73, -19, 55,
  88, 14, -2, 37, 84, 92, -221, -86, 23, 237, 27, 70, 8, 169, -39, -18, -81,
  81, 284, -227, -66, -118, 132, -240, 330, -77, 74, 61, 88, 38, -126, 75,
  -41, 195, 42, -240, 37, 35, -54, -48, 187, 42, -12, -38, 177, 66, -303,
  89, -81, 122, -10, 96, 234, 57, -7, -84, -107, -50, -24, 76, 385, 35, 182,
  54, 48, 76, 359, 53, 38, 110, 30, -43, 57, 94, -79, -66, -148, 132, -104,
  254, 98, 48, 202, 37, -24, -20, -58, 220, -247, 354, -91, 49, 24, -39,
  170, -89, 7, 215, 48, -6, -21, 187, 147, 204, 93, -35, 390, 86, 152, 21,
  67, 69, 93, 53, -259, -130, 213, -230, -18, 160, -158, -166, -219, -219]

theorem fractionalNearFrameSubtreeG1R0023_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0023Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0023Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0023Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0023_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0023LowerBoundTable : List ℤ :=
  [187, 273, 227, 337, -421, 255, 619, 140, 204, 617, 1035, 11, 521, 593,
  846, 448, -71, 123, 1099, 293, 395, 215, -172, -363, 1200]

def fractionalNearFrameSubtreeG1R0023LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0023Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0023LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
