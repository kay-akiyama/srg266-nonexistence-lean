import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0133`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0133Mask : ℕ := 1354093435753036

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0133Witness : Array ℤ :=
  #[66, 169, 30, -45, -158, 51, -86, 13, -85, -65, -80, 84, 112, 153, 49,
  83, 153, 175, -14, -10, -81, 92, 83, 116, -21, 118, -6, 53, 9, -52, 252,
  93, 79, -32, 52, -78, -32, 6, 8, -41, -46, 0, -20, -167, 45, 34, 141, 20,
  -21, -29, -14, -27, 1, 21, -36, -124, 63, -60, -121, 121, 143, -6, 4, 63,
  -67, 10, 82, 56, 153, -75, -21, 23, -55, 62, 86, 67, 57, 10, 82, -76, 35,
  37, -91, 30, -71, 42, 152, -13, -78, -17, 214, -37, -42, 60, -132, 178,
  32, 47, 53, 41, 79, 38, 142, 5, 260, 116, 132, 25, -10, 9, -69, -61, 36,
  -153, -48, -37, -58, 8, 17, 171, -27, -87, -57, 49, 106, -80, -53, -15,
  71, -69, 102, -13, 6, 21, 119, 100, -26, -18, -15, 42, -67, 102, -110, 47,
  -174, 56, -37, 14, -2, 82, -120, 172, -14, 42, -21, -8, 67, -31, -33, -68,
  -162, -63, 92, 219, 38, -48, -31, -4]

theorem fractionalNearFrameSubtreeG2R0133_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0133Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0133Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0133Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0133_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0133LowerBoundTable : List ℤ :=
  [48, -24, 253, 183, 249, 375, 120, 83, 328, 9, 56, 91, -199, 577, 563, 81,
  453, 319, 375, 74, 419, 101, 468, -21, 174]

def fractionalNearFrameSubtreeG2R0133LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0133Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0133LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
