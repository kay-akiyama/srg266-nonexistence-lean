import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0049`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0049Mask : ℕ := 554587422900440

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0049Witness : Array ℤ :=
  #[-77, 56, 45, -92, 13, 0, 38, 63, -4, -16, 97, -40, 65, 50, 3, 102, 189,
  79, 12, -100, -26, 7, -95, -23, 53, -84, -10, 30, -60, -95, -159, -26,
  113, 119, 116, 69, 53, -3, 0, 64, 40, 172, 176, -39, 38, 8, -33, -101,
  -25, -48, 14, -50, -56, -16, 0, -37, 139, -60, -70, 115, -102, -35, -39,
  -114, -59, 23, 65, 8, -61, -113, 17, 41, -46, -49, -6, -23, -135, 2, 11,
  123, 48, -17, 19, -18, 13, 32, 47, -60, 97, 30, 12, 109, 99, 31, -11, 54,
  87, -3, -118, 210, -60, -22, 38, -121, 65, -15, 24, -36, -84, -83, 55, 32,
  112, 69, 27, -41, -44, -79, 57, -100, 48, -36, 5, 164, -41, -55, 37, 50,
  -84, -15, 16, 70, -61, -27, -23, 10, 94, 145, -144, -133, 94, 41, 26, -55,
  -86, 98, 22, -5, 11, -49, -74, 60, 31, 52, 19, -40, -93, -152, 23, -14,
  -95, 0, -18, -13, -48, -55, 44, -27]

theorem fractionalNearFrameSubtreeG1R0049_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0049Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0049Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0049Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0049_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0049LowerBoundTable : List ℤ :=
  [-63, -131, -57, 6, -45, 134, 166, 74, 23, 74, -44, -163, -128, 80, 143,
  -75, 66, 70, 295, 10, 232, 71, -41, 11, 419]

def fractionalNearFrameSubtreeG1R0049LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0049Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0049LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
