import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0081`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0081Mask : ℕ := 5439065264065810

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0081Witness : Array ℤ :=
  #[471, 197, 205, 227, 381, 40, -51, 65, 53, 227, 53, -139, 74, 108, -766,
  -461, 4, 88, -57, -50, -2, -24, 11, -308, 246, -50, 391, 127, 390, 228,
  41, -129, -278, 324, 54, 271, -54, -163, -468, 38, 222, -367, 164, 107,
  315, 141, 279, 90, -301, -330, -344, -82, -100, 121, 215, -8, 16, -345,
  64, -151, 169, 284, 194, -222, 70, -275, 14, -13, 218, 78, 203, -56, 286,
  -69, 156, 13, -210, 211, -57, 78, -246, 540, 44, -97, -41, -198, 146, 52,
  387, 64, -212, -21, -19, 31, 277, 293, 69, 150, 661, 443, 3, -148, 102,
  128, -93, 111, 136, -720, -295, 116, 89, 248, 57, -193, 19, -539, -178,
  -49, 194, 177, 218, -126, -192, -257, 100, 161, -361, 201, 28, 45, -4,
  729, -378, 360, -412, 395, -249, -350, 464, 64, 50, -39, 285, -77, 261,
  22, 93, -49, 62, 637, 86, -45, 65, -433, 67, -289, 376, 101, -356, -202,
  603, 298, 134, 373, 206, -214, -669, 699]

theorem fractionalNearFrameSubtreeG5R0081_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0081Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0081Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0081Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0081_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0081LowerBoundTable : List ℤ :=
  [223, 393, 713, 582, 2, 677, 399, 2, 1, 1341, 147, -462, 596, 1431, -469,
  765, 314, 739, 538, 1580, -263, 433, 521, 1897, 309]

def fractionalNearFrameSubtreeG5R0081LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0081Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0081LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
