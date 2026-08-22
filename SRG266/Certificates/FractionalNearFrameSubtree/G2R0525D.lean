import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0525`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0525Mask : ℕ := 6771601887179793

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0525Witness : Array ℤ :=
  #[972, 54, 746, 59, 862, 764, 0, 19, -81, 27, 0, -235, 394, 600, 515, -27,
  290, -111, 100, 224, 155, 385, 166, 402, 218, 352, 320, 145, 171, 0, -221,
  160, -20, 212, -192, 135, 85, 172, 231, 672, -137, -63, 287, 44, 1137,
  -205, 255, -24, 49, -183, 10, 103, 121, 27, 58, -213, -245, 172, -104,
  -295, 179, 130, 41, -16, 372, 106, 63, 99, 0, -173, -105, -10, 31, 39,
  136, 6, 193, 198, -273, -121, 245, 205, -6, 244, 234, -22, -92, 21, -93,
  -200, -71, 249, 44, -44, -95, -51, -69, 168, 0, 14, 166, 278, 183, 80, 93,
  -109, -123, 418, 404, 579, 542, 439, 19, 146, 259, 151, -341, -29, -18,
  51, -295, 27, 87, 129, 111, 257, -48, -62, 193, 150, -39, 102, 116, 242,
  168, 40, 81, -126, -1, -50, 49, 120, 171, 176, 52, 105, -32, -7, 134,
  -117, 233, -47, 100, -287, 237, -237, -53, -119, 0, -329, -110, -89, -165,
  -228, 167, -21, -223, -868]

theorem fractionalNearFrameSubtreeG2R0525_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0525Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0525Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0525Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0525_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0525LowerBoundTable : List ℤ :=
  [1084, -65, -200, 21, 1490, 1676, 1865, 2750, 1166, 1002, 1175, 171, 708,
  -81, 2112, 542, 312, 1078, 322, -45, 949, 1716, 1555, 1563, 2025]

def fractionalNearFrameSubtreeG2R0525LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0525Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0525LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
