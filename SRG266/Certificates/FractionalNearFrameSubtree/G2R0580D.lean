import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0580`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0580Mask : ℕ := 6850664925137512

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0580Witness : Array ℤ :=
  #[-1099, -924, -175, -744, 782, -529, 487, 855, 179, 893, -299, 1512,
  -355, 259, -378, 234, 248, 410, 250, -226, 271, 391, 751, 855, 169, -639,
  -76, -726, -550, -1335, 886, 656, -454, 5, -630, 0, -814, 468, -480, 1767,
  -81, 790, 1218, -1184, -1012, 279, 263, -231, -694, -575, 509, 336, 970,
  1354, 1998, 1993, -3030, -401, 602, -237, -310, 537, -229, -410, -2875,
  1408, -714, 371, -319, 402, 207, 922, 147, -323, -803, 886, -1088, 320,
  788, 280, 1757, 1435, 149, 19, 578, 463, -810, 508, 106, 805, -705, -666,
  -74, 276, -1202, -250, 467, -181, -40, 555, -1277, -244, 356, 99, 471,
  -2177, -1023, -408, -68, -133, 574, 614, 688, 3824, -202, -76, 215, -289,
  -295, -516, -981, 853, 282, 38, 1019, 1134, -674, 651, -449, 1008, -744,
  199, -528, -158, 395, 416, 967, -208, 527, -499, -168, -302, 570, 747,
  -709, 654, 778, 905, 118, -1078, -90, -305, -412, 247, -55, -184, 489,
  -68, 390, 438, -1026, 1114, 59, -146, -2811, -635, 323, 261]

theorem fractionalNearFrameSubtreeG2R0580_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0580Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0580Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0580Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0580_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0580LowerBoundTable : List ℤ :=
  [249, 786, 31, 1666, 1665, -163, 32, 1937, 32, -4024, 1067, 1242, 1167,
  -2470, 3671, 2795, 2607, -519, 1640, 1293, 3838, 432, 100, 100, -175]

def fractionalNearFrameSubtreeG2R0580LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0580Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0580LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
