import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0471`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0471Mask : ℕ := 5809420988222040

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0471Witness : Array ℤ :=
  #[357, 65, 231, 47, 91, -445, -159, -141, -16, -187, -116, -122, 106, 174,
  77, 0, -189, -80, 102, -252, -140, 148, -183, -63, 79, 55, -286, -4, 62,
  69, 287, 242, 0, 326, -17, 0, 158, -77, -291, -2, -220, 128, -243, -27,
  -115, 155, 183, 126, -127, -57, 180, -96, 187, -342, 194, 266, -43, -289,
  408, 131, 288, 99, 113, 257, -318, -322, 307, -395, -88, -116, -1, -40,
  -10, -25, -42, 347, 70, -96, 93, 148, 77, -107, -258, -10, 102, 186, -406,
  -186, 214, -174, -318, -156, -81, 81, 86, 43, 44, 242, 24, -89, -138,
  -305, 113, 52, -394, 105, -156, -175, -437, -36, 65, 292, 295, 344, 227,
  -107, -275, -203, -164, -17, -56, 37, 14, 92, 7, 22, 141, 436, -141, 236,
  18, 232, 62, 221, 135, 120, 257, -85, 88, -32, 111, -140, 43, -135, 306,
  -74, -415, 133, 77, 246, -206, -55, -83, 1, 22, 250, 368, 162, -154, 86,
  309, 193, -34, -299, -5, -22, 68, 105]

theorem fractionalNearFrameSubtreeG2R0471_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0471Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0471Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0471Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0471_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0471LowerBoundTable : List ℤ :=
  [-167, 449, 143, 0, -428, 280, -284, 266, 1, 10, 335, 265, 981, 358, -583,
  536, 787, -1328, 814, 784, 503, -323, -139, 699, 635]

def fractionalNearFrameSubtreeG2R0471LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0471Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0471LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
