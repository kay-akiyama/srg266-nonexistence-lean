import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G4R0015`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0015Mask : ℕ := 4877206387771653

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0015Witness : Array ℤ :=
  #[-418, 131, -523, -231, -354, -247, -218, 0, 169, -582, -582, -536, -198,
  350, 612, 1385, 1066, 1, 1794, 827, 915, -836, 488, -746, 197, -175, 221,
  -557, 0, -1391, -1090, 443, 567, 546, -144, -346, 809, -366, 0, 102, -403,
  -93, 282, 624, -376, 872, -324, 193, -656, -1051, -1400, 189, 483, -360,
  1024, 1237, 845, 117, 764, 207, 36, -280, -600, -1611, -213, 429, -8, 433,
  365, -99, 828, 476, 635, 758, 194, -547, -35, -152, -249, -461, -110, 135,
  -639, -264, 1293, 703, -432, 359, 517, 287, 642, 425, -511, -128, -165,
  -489, 245, -602, 633, 312, -578, -15, -590, 27, 628, -593, -1157, -784,
  87, 528, 985, 541, 26, 748, 609, -171, -901, -419, -1131, 233, 0, -35,
  467, 1358, 479, 318, -505, -447, 688, -434, 654, 2, -812, -4, 225, -683,
  815, 786, -532, -416, 1107, -172, 481, -710, 430, 572, 272, 429, -455,
  -327, 58, 301, -928, -203, 917, 112, -256, -263, -317, 274, 442, -252, 0,
  561, 208, 372, -723, 876]

theorem fractionalNearFrameSubtreeG4R0015_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0015Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0015Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0015Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0015_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0015LowerBoundTable : List ℤ :=
  [-241, 495, 1060, -174, 1216, 144, -480, 32, 282, 2537, 511, 1893, 998,
  4021, 127, 1932, 5123, 4712, -1620, 102, -126, 478, -1011, 1734, -1345]

def fractionalNearFrameSubtreeG4R0015LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0015Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0015LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
