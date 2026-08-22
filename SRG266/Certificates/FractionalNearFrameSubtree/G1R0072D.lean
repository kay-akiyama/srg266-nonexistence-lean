import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0072`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0072Mask : ℕ := 866326664555529

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0072Witness : Array ℤ :=
  #[70, -81, -39, 0, -121, -245, 85, 34, 223, 47, 92, -6, -226, -69, 35, 0,
  -69, -176, -117, 169, 68, 113, -110, -21, 18, -26, -95, 0, 29, -8, -89,
  68, 54, 84, -39, 78, -143, -128, 55, -67, -176, 42, -27, 39, 97, 94, -80,
  43, -90, 43, 46, -81, -3, 39, 6, -159, 52, 110, -130, -26, 26, -117, -132,
  149, -1, -19, 192, -103, 77, 15, 65, 100, 26, -20, 0, 34, 111, -44, -1,
  -16, -64, -65, -79, 63, -16, -46, 213, -81, -39, 9, 89, 8, 42, -124, -65,
  32, 121, 57, -49, 24, 52, 103, -63, 126, 78, 78, 416, -10, 48, 74, -16,
  -150, 89, 51, 19, 299, -92, -22, 3, -45, 100, 83, 68, -253, 28, 55, 93,
  55, -2, -74, 201, 56, 47, -39, -109, -174, -92, 33, 37, 45, 87, 219, -24,
  108, -34, 168, -38, 53, -57, 79, -66, 177, -146, 136, 17, 31, 78, 71, 38,
  -113, -62, -33, -23, -16, 187, 13, 109, -143]

theorem fractionalNearFrameSubtreeG1R0072_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0072Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0072Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0072Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0072_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0072LowerBoundTable : List ℤ :=
  [71, 228, 456, 169, 0, -11, 2, 3, 86, 598, 175, 240, 1, 497, 446, 210,
  365, -3, -193, 20, 10, -106, 114, 121, -280]

def fractionalNearFrameSubtreeG1R0072LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0072Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0072LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
