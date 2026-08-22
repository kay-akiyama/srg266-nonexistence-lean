import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0173`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0173Mask : ℕ := 6863963556848786

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0173Witness : Array ℤ :=
  #[-89, -247, -127, 67, 157, 100, 108, 167, 98, -75, 289, -205, -199, -313,
  -217, 43, -161, -141, -244, -143, -32, 155, 79, 58, -183, -34, -93, 74,
  257, 98, 257, 175, 121, 49, 27, -25, -70, 153, 83, -40, -169, -294, -20,
  -21, -23, 70, 106, 195, 47, 98, 112, 80, 86, -286, 182, 234, 209, -186,
  22, -4, -346, 75, -180, -51, -328, -431, 80, -95, 0, 104, -95, -224, -39,
  222, 91, 166, 156, 182, -303, -64, 232, 102, 191, -46, 78, -204, -295,
  -16, 125, -6, -42, -215, -182, -141, -242, 148, 40, -164, 78, 40, 55,
  -171, -85, -78, 60, -243, 77, -281, -56, 379, -50, 111, 81, 204, 43, 204,
  81, 203, -65, -80, -275, 294, -60, 23, 153, -127, -24, -101, -116, 220,
  102, -117, -297, 265, -123, -53, 207, 158, 202, 344, 189, 443, 57, 68,
  -248, 98, 272, 311, 342, 0, 361, 112, 29, 30, 45, 215, -171, 131, 219,
  -52, 241, 23, 219, 35, 30, 139, -30, 141]

theorem fractionalNearFrameSubtreeG3R0173_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0173Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0173Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0173Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0173_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0173LowerBoundTable : List ℤ :=
  [-79, 902, 1, 84, 278, -9, 225, 1, 2, 1222, 839, 1484, 1263, 369, 337,
  391, -21, -633, 496, 64, 146, 363, -164, -451, -317]

def fractionalNearFrameSubtreeG3R0173LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0173Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0173LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
