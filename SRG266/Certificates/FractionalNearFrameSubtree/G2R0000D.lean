import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0000`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0000Mask : ℕ := 237282585399813

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0000Witness : Array ℤ :=
  #[193, 70, 162, 16, 94, -13, -121, -233, -121, -115, -203, -230, 218, 6,
  135, 93, 26, -109, 120, -18, 8, 52, 32, 103, 1, -32, -56, 19, -89, -52,
  95, -9, -34, -62, -15, -9, 20, -42, -23, 179, 187, 169, -188, -79, -149,
  -295, 154, -55, -22, 86, -13, -23, -22, -51, -51, 32, -17, 11, 2, -52, 5,
  -47, 0, 104, -84, 72, 48, -33, 82, 24, -68, 45, -27, -72, 106, 20, -18,
  -101, 12, 35, 86, -23, 48, 9, 1, 87, 12, -3, 42, 47, 40, 20, -57, -73, 38,
  7, 82, -9, -107, -15, 74, -2, 25, -41, -18, 12, 47, 89, 0, -77, -40, 18,
  -61, -24, -62, -25, -58, -36, 41, 0, -23, -71, 24, 8, 14, 45, -2, -15,
  -37, -6, 45, 28, 174, -6, 49, -78, -27, -62, 14, 18, 11, 18, 3, -89, -7,
  -26, -23, 127, 32, 20, -10, 70, 44, 35, 110, 104, 19, -93, 45, 5, 25, 131,
  -127, -85, -10, 18, 23, 179]

theorem fractionalNearFrameSubtreeG2R0000_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0000Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0000Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0000Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0000_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0000LowerBoundTable : List ℤ :=
  [-67, 120, 2, 2, 2, -114, 175, 18, 135, 91, 130, 51, -219, 255, 193, 120,
  -46, 93, -84, 9, 9, 24, 320, 0, 11]

def fractionalNearFrameSubtreeG2R0000LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0000Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0000LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
