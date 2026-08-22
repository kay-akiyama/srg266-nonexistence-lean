import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G4R0008`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0008Mask : ℕ := 1382720473104451

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0008Witness : Array ℤ :=
  #[-429, -583, -306, -67, 268, -150, -314, 52, -619, 252, 199, 119, 184,
  -75, 272, 213, -761, 55, -32, -408, -169, 365, 176, 354, -44, 116, -185,
  -193, 0, -740, -29, 285, 66, -180, 306, -409, 21, -116, -284, -269, 27, 0,
  -68, -469, 75, -13, -167, 264, -217, 533, -214, 132, -60, 696, 701, 132,
  136, -99, 676, -7, 117, 432, -125, -72, -14, 868, -316, -188, -157, -319,
  463, 396, 225, -665, 806, 541, -323, 722, 633, 963, 56, 110, -19, -1, 105,
  479, 170, 10, -831, 284, -226, 411, 405, -385, 22, -19, 700, 571, 652,
  -548, 545, 42, -365, 94, -467, -746, 4, -205, 425, -998, -182, -320, 103,
  723, -30, -239, 342, -42, -257, 148, -212, -622, -610, 78, 384, 861, -437,
  0, -169, -272, -215, 341, -647, -2, -59, -57, 631, 1005, 68, 127, 866,
  -58, 464, -690, 792, 887, -714, 71, 965, -493, 101, 222, -142, -36, -293,
  4, -304, -354, -196, 148, 185, 468, 15, -398, 335, 128, -618, 178]

theorem fractionalNearFrameSubtreeG4R0008_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0008Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0008Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0008Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0008_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0008LowerBoundTable : List ℤ :=
  [-281, 609, 221, 338, 710, 620, 257, 3, -333, 963, 712, 551, -1997, 596,
  -173, 1474, 9, -130, 1471, -960, 2098, 10, 1948, 1537, 1380]

def fractionalNearFrameSubtreeG4R0008LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0008Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0008LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
