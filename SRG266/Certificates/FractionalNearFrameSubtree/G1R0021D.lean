import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0021`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0021Mask : ℕ := 450640486248965

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0021Witness : Array ℤ :=
  #[0, 36, 227, 80, 102, -205, -169, 107, 71, -43, -28, -179, 78, -112, -61,
  50, 0, -43, -60, -127, 12, -104, -275, 72, -160, 204, -226, -154, 270, 91,
  190, 298, 152, 187, 74, 89, -250, -83, 19, -166, -42, -146, -12, -97, 31,
  122, -16, 73, 54, 90, -107, 31, 19, 86, -29, 0, -33, -120, -96, 120, 0,
  39, 253, -150, -138, -89, -48, 82, -144, 35, -90, 97, -47, 33, 34, 119,
  -26, 0, -35, -55, -194, -135, -218, -166, 168, 117, -33, 84, -12, -16,
  115, -245, 49, 133, -41, -78, 177, 48, -93, -123, -98, -167, -14, 117,
  119, 181, 163, -3, 48, 58, 200, 105, 21, 42, -163, 25, -89, 85, 1, 59,
  -102, 56, 41, 135, 111, 97, -29, -29, -8, 97, -50, 0, 131, -141, 195, 29,
  -6, 114, 114, -73, 28, 183, 81, -7, -23, 129, -45, 225, 53, -10, 46, 93,
  52, 167, 28, -4, 20, -26, -94, -42, 75, -80, -47, 133, -75, 34, -83, 37]

theorem fractionalNearFrameSubtreeG1R0021_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0021Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0021Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0021Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0021_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0021LowerBoundTable : List ℤ :=
  [-62, 277, 125, -175, -201, -31, 1, 268, 3, 525, 579, 497, 433, 328, 439,
  385, 249, -352, 386, 9, -288, 9, 515, 521, -70]

def fractionalNearFrameSubtreeG1R0021LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0021Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0021LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
