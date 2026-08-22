import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0005`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0005Mask : ℕ := 548822501466181

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0005Witness : Array ℤ :=
  #[463, 407, 593, 416, 267, -171, -77, 0, -207, -739, -188, 402, -180,
  -320, -325, -32, -450, -780, 256, -268, -576, 231, 568, 418, 345, -334,
  366, 131, 170, 465, 195, 156, -245, -431, 1011, -101, -23, -355, 548, 196,
  -420, -242, -282, 0, 211, 228, -8, -766, -188, -508, 560, -388, 865, 468,
  352, 408, 646, -262, 121, -263, -120, 758, 524, 422, 17, 336, -93, -327,
  219, -434, 156, 357, 500, -107, 183, -146, -166, -73, 288, 671, -302,
  -959, -172, -128, 0, -291, -64, -339, 159, -267, 368, 310, 288, -100, 20,
  -221, 97, 32, 304, 416, 331, 62, 78, -120, 31, 426, 329, 177, -436, -37,
  -388, -376, -526, -226, 354, 132, 382, 183, 210, -199, -446, 346, 286,
  -491, -703, -760, 393, 237, -245, -454, 82, -487, -460, -164, 129, -249,
  -343, 799, 76, -5, 18, 405, 651, 622, -74, 391, -301, 379, 111, 413, 449,
  -574, 182, 487, -393, -163, -344, -149, 180, -41, -330, 298, 110, 38,
  -168, -248, -123, -18]

theorem fractionalNearFrameSubtreeG5R0005_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0005Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0005Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0005Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0005_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0005LowerBoundTable : List ℤ :=
  [-137, -112, 32, 418, 588, -181, 703, 194, 877, -927, 443, 954, 339, 451,
  -266, -1261, 348, 3026, 1306, 101, -793, 1093, 1397, 1185, 563]

def fractionalNearFrameSubtreeG5R0005LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0005Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0005LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
