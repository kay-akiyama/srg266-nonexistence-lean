import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0107`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0107Mask : ℕ := 5261837670208152

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0107Witness : Array ℤ :=
  #[29, 128, 103, -82, 74, -70, 48, -91, 119, -24, -91, 173, 31, -65, 161,
  -143, 315, -38, 33, 132, -158, -117, 186, 5, -22, -377, -379, -327, -40,
  76, -17, -85, 135, -81, 126, -202, 44, -10, -102, 0, -197, 115, -81, 41,
  76, 32, -29, -35, -80, 269, -346, -363, -295, -89, -64, -74, 178, 276,
  -65, -81, 142, 252, -71, 153, 103, 203, 117, 113, -491, -10, -212, 69,
  -340, -237, 58, 167, 55, -56, 27, 101, 100, 1, 148, -97, 22, -235, 125,
  102, 7, 29, 192, -51, 56, -110, 103, -81, -295, 125, 71, -135, -213, -101,
  -46, 108, -192, -20, -92, 58, -41, 113, -62, -25, -83, 325, -51, -7, -17,
  -71, 108, -257, -375, -316, -81, -177, 181, 209, 209, -33, 139, 26, 32,
  137, -65, 158, 51, -66, 100, -121, 217, -483, -193, 195, 132, 88, -159,
  93, 158, 12, 18, -236, -47, -62, -42, 101, 25, -50, 14, -86, 152, 75, -94,
  223, -7, 204, 206, -82, -97, -41]

theorem fractionalNearFrameSubtreeG3R0107_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0107Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0107Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0107Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0107_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0107LowerBoundTable : List ℤ :=
  [-329, -34, -145, -193, 34, 2, -204, 2, -672, -72, 158, 282, -563, 204,
  -433, 218, -872, 9, 115, 203, -934, 646, 761, 623, -66]

def fractionalNearFrameSubtreeG3R0107LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0107Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0107LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
