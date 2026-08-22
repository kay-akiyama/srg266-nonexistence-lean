import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0128`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0128Mask : ℕ := 5863460659071394

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0128Witness : Array ℤ :=
  #[382, 179, -8, 33, -100, -27, -143, -114, 25, -32, -210, -2, 71, 45, 0,
  273, 341, -60, -135, -106, -132, -64, -106, 28, -107, 88, 107, 9, 211,
  196, 202, 366, 242, 99, 100, -170, -726, -45, 83, 382, 131, -359, -216,
  -465, -318, -44, -51, -38, -29, -14, -47, 190, -65, 283, 70, 85, -343, 53,
  -66, 80, 19, 0, 402, -258, 117, 440, 140, 141, 253, 47, -103, -113, 171,
  89, -81, 217, -27, -31, 74, 215, 240, -7, 72, 21, 123, -17, -107, -168,
  -83, -237, 109, 205, 91, 113, 28, 216, -89, 0, 116, -58, 0, 82, 172, 0,
  346, 63, 45, 7, 195, 7, 50, 122, 240, 210, -283, 184, 373, 240, 81, 31,
  -95, -62, 210, 211, 243, -20, -124, 64, 198, 473, 53, 51, -67, 255, 33,
  250, -223, -21, -90, -123, 62, -135, 51, 335, -169, 132, 105, -158, 95,
  189, 42, 72, 224, 216, 351, -115, 267, -3, -56, 164, -54, 106, 46, -26,
  146, -72, 173, -302]

theorem fractionalNearFrameSubtreeG5R0128_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0128Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0128Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0128Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0128_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0128LowerBoundTable : List ℤ :=
  [291, 725, 731, 246, 405, 573, 807, 525, 1, 1911, 1268, 138, 403, 684,
  461, 999, 9, 672, 584, 836, 171, -230, 580, 922, -28]

def fractionalNearFrameSubtreeG5R0128LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0128Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0128LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
