import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0391`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0391Mask : ℕ := 5739956187546762

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0391Witness : Array ℤ :=
  #[-459, 276, 630, -1, 72, -366, 498, -93, -218, 56, 751, 95, 0, 96, -74,
  -578, 518, 318, 270, 326, 789, -58, -182, 379, -1041, -302, 82, -207,
  -282, 224, -153, -264, 356, 528, 289, 562, 594, 500, -70, -137, 189, 60,
  533, -217, 557, 1218, 380, -854, -710, -534, 228, 612, 473, -300, 878,
  162, -444, -744, -39, 59, 410, 814, -6, 941, -700, 342, 254, -708, 89,
  473, -214, -333, -73, 931, 166, 195, 199, 53, 397, 506, 245, 184, 15, 359,
  789, 172, 606, -263, -614, -164, 1012, -569, -193, 337, -785, -550, 42,
  48, 135, -65, 599, 626, -59, 276, 413, -504, -483, 66, -61, -531, 482,
  -417, -324, -548, -274, -527, -42, -297, 102, -975, 213, -344, 404, 288,
  129, 549, 106, -445, 364, -221, 575, 370, 457, -226, -694, 644, -78, 19,
  521, -518, 536, -44, 225, -923, 1115, 394, 160, -75, 196, -366, 266, -281,
  463, 99, 128, 400, 320, -169, 0, 189, 74, 169, 206, 1181, 433, 422, 641,
  661]

theorem fractionalNearFrameSubtreeG2R0391_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0391Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0391Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0391Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0391_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0391LowerBoundTable : List ℤ :=
  [504, 975, 2003, 474, 420, 1300, -342, 1521, 774, 998, 771, 1192, 49,
  4107, 3189, 5584, -282, 1092, -471, 3553, 770, 1371, 1746, -332, 3619]

def fractionalNearFrameSubtreeG2R0391LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0391Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0391LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
