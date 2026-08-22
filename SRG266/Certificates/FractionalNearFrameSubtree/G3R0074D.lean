import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0074`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0074Mask : ℕ := 2355542301053009

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0074Witness : Array ℤ :=
  #[-188, -9, -291, -331, -301, -21, 195, 267, 428, 313, 368, 425, 45, -108,
  0, 118, 19, 132, 98, 452, 60, -81, 39, 121, 96, 69, 182, -5, -18, -103,
  -165, 159, 271, 233, 32, 27, 375, 105, -521, -415, -332, 295, 450, 428,
  537, -473, -413, 284, 48, 228, 153, 178, -396, -146, -8, 330, -162, -250,
  358, 251, -173, 98, -24, 150, -41, 51, 275, 54, -18, 81, -18, 169, -7,
  -42, 134, -6, -33, 270, 138, 268, 94, -36, 86, 93, 21, -2, 161, 222, -1,
  194, 91, 2, -56, -7, 87, 39, 34, 80, 76, 117, -47, -78, -160, -157, -261,
  -169, -140, 92, 37, 159, 87, -95, -246, -113, -232, -53, 40, 2, 207, 214,
  238, 162, -28, 87, 181, 138, -55, 102, 73, 26, 69, 64, -167, -179, 20,
  -28, 223, 134, 211, 105, 16, 18, 80, -130, 19, 85, -123, 104, -137, -95,
  -164, 140, 178, 33, -65, 0, 124, 54, 105, -8, 22, 151, -327, 121, -115,
  -13, -288, 5]

theorem fractionalNearFrameSubtreeG3R0074_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0074Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0074Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0074Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0074_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0074LowerBoundTable : List ℤ :=
  [371, 167, 413, 556, 382, 325, 338, 581, 623, -262, 337, 450, 699, 44,
  175, 772, 1068, 300, 1404, 76, 1418, 11, 86, 259, 1030]

def fractionalNearFrameSubtreeG3R0074LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0074Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0074LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
