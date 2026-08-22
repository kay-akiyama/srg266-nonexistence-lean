import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0025`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0025Mask : ℕ := 953948124938566

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0025Witness : Array ℤ :=
  #[75, 118, -4, -214, 81, 117, -21, -115, 47, 24, 45, -68, 3, -38, 189,
  164, -27, 130, -265, 0, -6, 96, -69, 151, 97, 79, 29, 48, -9, 29, 117, 73,
  130, -160, -53, 95, 94, -117, -91, 56, -26, 0, -59, 47, 0, 111, 345, 97,
  -137, 110, -122, -12, 0, 22, 3, 14, 54, 27, 33, 72, -41, -36, -90, 44,
  -37, 0, 28, -59, 29, 128, 121, -84, -105, 184, 27, 201, 214, -43, 49, 22,
  36, 88, 114, 55, -62, 7, 21, 62, 48, 209, 236, 220, 120, 92, -15, -54, 22,
  126, 59, 64, 25, -135, -9, -141, 26, 44, -35, 67, 56, 69, 33, 77, 266,
  133, 120, -79, 207, -94, -47, -65, 154, 54, 135, 29, 82, -55, 97, 61, 8,
  193, 43, -36, 45, 18, 116, -20, -3, 278, 85, -45, 81, -78, -259, 82, 53,
  8, -19, -145, -149, 41, 56, 25, -109, 40, 315, -39, -98, -64, 260, 129,
  -268, -110, 84, 0, -70, -126, -46, 340]

theorem fractionalNearFrameSubtreeG3R0025_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0025Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0025Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0025Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0025_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0025LowerBoundTable : List ℤ :=
  [317, 188, 550, 435, 521, 199, 313, 303, 405, 253, 620, 162, 488, 958,
  491, 210, 629, 516, 234, 251, 236, 79, 238, 9, 446]

def fractionalNearFrameSubtreeG3R0025LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0025Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0025LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
