import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0004`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0004Mask : ℕ := 242903760357897

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0004Witness : Array ℤ :=
  #[324, 394, 229, 154, 214, 92, -180, -35, 3, -71, -304, -124, 0, -231,
  -70, 100, -278, -52, -65, 29, 30, -94, -213, 225, 8, 14, -1, -129, 134,
  -92, 128, 307, -3, 119, -181, -23, 168, 21, -169, -79, 78, 188, 263, -39,
  -104, -75, -173, 0, 38, -60, 164, -1, 102, 27, -98, -47, -52, -68, 93,
  -128, -160, 127, 108, -217, -107, 152, -122, -213, 29, 23, 185, 87, -24,
  86, 32, 136, -30, -125, 5, 70, 3, 33, 72, 48, -49, 105, -171, -16, -73,
  -92, 167, -164, 201, 14, -155, 93, 142, -23, 37, 26, -3, 96, 132, -18, 85,
  35, -7, -43, -9, -82, 114, 2, -107, -49, -23, 92, -463, -84, 156, -76,
  -79, -95, -86, 182, -44, -26, -23, 87, -173, 21, 278, -70, 44, -149, -73,
  -161, -60, 296, -24, -38, 49, -63, 8, -63, -38, 74, 154, 62, -12, -7, -48,
  49, 60, 41, 204, -140, 91, -134, 164, 41, 89, 10, 250, -361, -10, 32, 10,
  -7]

theorem fractionalNearFrameSubtreeG1R0004_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0004Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0004Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0004Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0004_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0004LowerBoundTable : List ℤ :=
  [-178, 2, 69, 178, -1, 2, -26, 353, 90, -110, -180, -152, -349, 710, 9,
  105, 25, 77, -224, 462, 458, -439, 413, 8, 67]

def fractionalNearFrameSubtreeG1R0004LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0004Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0004LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
