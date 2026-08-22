import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0251`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0251Mask : ℕ := 5355430609535750

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0251Witness : Array ℤ :=
  #[-18, -291, 406, 156, 271, -198, -1689, -642, -437, -292, -922, 413, 397,
  382, 418, 218, 183, -177, 108, 220, -93, -858, -92, -101, 21, 255, -552,
  -43, -319, -158, 146, 0, 106, 7, -104, 176, -241, 599, 340, 148, -434,
  -211, 179, -106, 249, 508, 302, 13, -245, -174, -298, -100, -287, 232, 9,
  101, 420, 247, -243, -251, 277, -626, -809, 186, 210, -1, 58, 628, -972,
  -200, 535, -28, 227, 196, -29, -338, 237, 118, -134, -377, -496, -23,
  -368, 233, 58, 97, 263, -89, 557, 190, 145, -38, -52, -280, 610, 34, 41,
  -183, -171, -223, 33, -46, 22, -175, 528, 300, -12, -244, -72, 199, 208,
  405, 520, 656, 1017, 192, -149, 285, 121, -230, 450, 491, 458, -229, -37,
  -100, -510, 61, 246, 475, 11, -104, -19, -212, -639, -245, -118, 84, -231,
  -47, 89, -171, -2, -329, -76, -63, 222, 79, -123, 194, -125, 69, 261, 714,
  -16, -367, 190, 189, 292, -452, -151, 308, -470, 83, -8, 28, -1121, -328]

theorem fractionalNearFrameSubtreeG2R0251_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0251Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0251Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0251Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0251_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0251LowerBoundTable : List ℤ :=
  [-407, 33, -166, 31, 31, 32, -979, 642, -56, 2253, 383, -103, 532, 101,
  265, 377, 1048, -736, 697, 181, 340, -1393, 539, -1386, 100]

def fractionalNearFrameSubtreeG2R0251LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0251Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0251LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
