import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0117`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0117Mask : ℕ := 969510041002216

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0117Witness : Array ℤ :=
  #[-92, -150, -11, -237, -67, 155, 137, 42, 206, 36, 138, -77, -37, -28,
  -197, -144, -61, 127, -81, -33, 63, 201, 349, -47, 20, -20, -8, 176, 101,
  -252, 131, 148, 123, -63, -281, 9, 41, 320, 263, -1, -191, 333, 88, 11,
  67, 130, -23, -391, -406, -268, 334, 127, 341, 288, 7, 0, 82, -93, -51,
  93, 21, -45, -143, 104, -32, 77, -17, -35, -42, -22, 3, 53, 85, -198, 114,
  -181, -392, 149, 9, 36, 112, 332, 119, 78, 149, 132, -172, 68, 257, 51,
  -15, -24, 132, 119, -102, 23, -124, 84, 336, -49, 163, -243, 9, -60, 12,
  -49, -303, -72, -255, 43, -163, 204, 90, 111, -166, 104, 52, -69, 78,
  -161, -143, 40, 34, 108, -163, 127, -147, 252, 149, -237, -397, 68, 94,
  -12, 154, -18, -112, -225, -58, 59, 126, -5, -27, -77, -75, 66, 186, 57,
  292, 63, -105, 355, 139, 243, -193, -171, -142, 156, 192, -26, 28, 0,
  -292, -33, -71, -47, -134, 61]

theorem fractionalNearFrameSubtreeG1R0117_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0117Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0117Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0117Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0117_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0117LowerBoundTable : List ℤ :=
  [-94, 128, 122, 243, 102, 126, 2, 1, 2, 13, -240, -411, 356, 698, 721,
  213, 460, 8, 657, 398, 612, 470, -296, 411, -77]

def fractionalNearFrameSubtreeG1R0117LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0117Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0117LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
