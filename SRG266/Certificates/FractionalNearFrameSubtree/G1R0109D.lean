import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0109`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0109Mask : ℕ := 963537033347412

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0109Witness : Array ℤ :=
  #[-34, 44, -56, -1, -28, 119, 49, 19, 37, -28, -10, 156, 101, -203, 134,
  49, 56, 51, -24, 12, 85, 39, 8, -46, 63, -21, 2, -64, 26, 85, -19, 84,
  -12, -32, 37, 39, -158, -136, 0, -142, 106, 94, 9, 96, -33, -90, -32, -11,
  -50, 5, -138, -23, 11, -8, 56, 26, 0, 81, 5, 51, -9, -90, -83, -112, 170,
  -56, -95, -136, -21, -81, 91, 24, -73, -29, 27, -28, -11, -94, 47, 49, 40,
  16, -71, -158, -195, -47, -56, 51, 18, -59, 60, -79, 22, 0, 87, 70, 103,
  21, 66, -34, 116, -140, 2, -54, -97, -59, 80, 94, 85, 6, -46, 53, 63, -44,
  102, 11, 91, 36, -30, -156, 110, -41, 29, 11, 1, 170, -69, 113, 33, 63,
  108, -37, -8, -95, -10, 136, -27, 108, 72, -73, -79, 6, -83, 98, 121, 107,
  122, -51, -204, -131, -42, 103, -36, 139, 70, 54, -102, -4, 144, -31,
  -156, 81, -162, 162, 67, -56, -58, 239]

theorem fractionalNearFrameSubtreeG1R0109_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0109Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0109Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0109Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0109_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0109LowerBoundTable : List ℤ :=
  [-61, 227, -239, 2, -13, 204, 284, 24, -46, 59, 405, 503, 63, 11, -75,
  -215, -224, 72, -178, 83, 9, -82, 10, 500, 552]

def fractionalNearFrameSubtreeG1R0109LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0109Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0109LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
