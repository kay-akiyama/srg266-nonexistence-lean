import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0042`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0042Mask : ℕ := 2517021043434499

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0042Witness : Array ℤ :=
  #[300, -219, 539, -204, -106, 63, 177, -22, -127, 240, -304, 458, 97, -8,
  -136, 345, -23, -177, 207, -319, -168, -7, 647, 499, 150, 919, 30, -501,
  178, -278, -610, 118, -714, -201, -415, -924, -161, -461, 699, 843, 931,
  -270, -438, -424, 561, -140, -657, -392, -78, 694, -251, 341, 415, -525,
  -300, 357, -120, 859, 410, 489, 525, -108, 16, -96, 219, -4, 253, -253,
  -352, 495, 1, -303, 492, -755, -526, -189, 363, -40, 415, 266, 402, -518,
  575, 19, -53, 211, -219, 278, 396, 805, 208, -132, 415, 433, -497, -79,
  -169, -145, 638, 563, -664, -7, -236, -80, -39, 306, -377, -238, 256, 681,
  -280, 213, 489, 789, 338, 41, 43, -672, -563, -1009, 616, -102, 404, 906,
  -934, -134, 275, -155, -607, -1075, -189, 500, 123, -534, 670, -875, 601,
  -56, -90, 200, -396, 193, -365, -167, 68, 311, -313, -595, -24, -103,
  -860, 478, 486, -431, -114, -122, 171, 577, 0, 25, -10, 439, 601, 114, 80,
  715, 718, 613]

theorem fractionalNearFrameSubtreeG5R0042_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0042Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0042Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0042Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0042_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0042LowerBoundTable : List ℤ :=
  [115, 420, 32, 33, 33, 622, 246, 32, 1502, 101, 100, -250, 352, 736, 804,
  913, 872, -556, -600, 3453, -699, 1822, 1582, 1072, 1928]

def fractionalNearFrameSubtreeG5R0042LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0042Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0042LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
