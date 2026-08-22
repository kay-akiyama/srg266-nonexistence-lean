import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0149`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0149Mask : ℕ := 1376225116234890

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0149Witness : Array ℤ :=
  #[-76, -69, 167, 232, 143, -62, -183, -111, -533, -335, -299, 20, 142,
  297, 414, 195, 208, 213, -172, 193, 342, 7, 159, 100, -95, 92, -128, -343,
  110, -146, -211, 273, -100, -79, 136, 105, 188, 38, -123, 61, -135, 606,
  -392, -33, 173, 75, 233, 13, 101, 127, 138, 47, 2, -61, -32, -480, 114,
  179, 2, 401, 374, -196, -173, 360, 204, -52, -93, -122, -50, 51, 123, 204,
  179, 145, -201, -27, 396, -83, -146, -35, -46, -10, -67, -49, -146, 464,
  -47, -170, -44, 50, -55, -259, 59, -26, 198, -477, -53, 44, 74, 80, 186,
  117, 278, 78, 56, 94, 326, 0, -241, -219, -249, 94, 6, 124, -28, 200, 130,
  -2, 115, -58, -21, 59, 213, -608, 99, -164, -19, 24, -209, -57, -63, 71,
  64, 361, -22, -397, 276, 268, 90, 42, -93, 587, 198, 122, 39, 117, 101,
  367, -481, 151, 127, 51, -559, 56, 31, 160, -136, 58, -17, -197, -100,
  169, 557, 63, -169, -603, 105, -186]

theorem fractionalNearFrameSubtreeG2R0149_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0149Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0149Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0149Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0149_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0149LowerBoundTable : List ℤ :=
  [152, 3, -127, 186, 575, 224, 150, 181, 399, 457, 170, 753, 134, 363, -2,
  -213, 140, 445, 210, 314, 909, 946, 904, 9, 721]

def fractionalNearFrameSubtreeG2R0149LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0149Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0149LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
