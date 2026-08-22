import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0133`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0133Mask : ℕ := 6833387698031378

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0133Witness : Array ℤ :=
  #[563, 88, -86, 104, 176, 4, -295, 226, -417, -56, -304, 0, 16, -236, 285,
  3, 101, 276, 91, 811, -453, 113, 503, -287, -69, 37, -35, -173, -694, 362,
  367, 103, 554, -1010, -159, 237, -42, -208, -141, 437, 1124, -381, 87,
  -776, 195, 426, 850, 143, -654, -274, -80, -253, -13, 686, -513, -291,
  252, -90, -25, 418, -233, -288, -83, -685, -310, -145, -489, 1156, -464,
  563, -114, 194, 264, 491, 759, -687, -191, 799, 88, -646, -13, 423, -129,
  -686, -451, 463, 187, -125, 617, 374, -99, 397, 200, 705, 272, 944, -818,
  -125, 223, -398, 231, -105, 531, 459, 320, -66, -245, 794, 659, -926,
  -1363, 84, 477, 1214, 179, 437, 130, -20, -379, 843, 196, -592, 147, -283,
  646, 262, 298, -614, -170, 904, -8, -157, 145, 82, -2, -834, 508, 553,
  -18, 253, -196, 811, 254, 608, -49, 617, -881, 215, 42, -120, 873, 487,
  -36, -503, 164, -871, -629, 306, 492, 814, -535, -372, -945, -133, 741,
  353, -247, -445]

theorem fractionalNearFrameSubtreeG3R0133_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0133Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0133Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0133Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0133_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0133LowerBoundTable : List ℤ :=
  [165, 686, 190, 32, 1261, 1121, 31, 1005, 31, 2383, 839, 1516, -330, 2071,
  -527, 99, 1855, 1995, 1726, -231, 1915, -385, 2704, 100, 100]

def fractionalNearFrameSubtreeG3R0133LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0133Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0133LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
