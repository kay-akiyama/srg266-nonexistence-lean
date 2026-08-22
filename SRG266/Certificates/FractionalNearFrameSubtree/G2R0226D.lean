import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0226`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0226Mask : ℕ := 2496455801147632

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0226Witness : Array ℤ :=
  #[-963, 74, 712, 267, 489, -792, -733, -130, 677, -444, -230, -1369, -995,
  352, 529, -712, 729, 214, -245, 1182, 501, 747, -615, 592, -1518, -1985,
  1260, -1433, 993, -266, -75, -1608, -932, 546, 1487, 0, 1263, -291, -911,
  665, -95, 158, 1037, 245, -924, 971, -193, -387, -469, 474, 735, -1362,
  -398, 1653, 147, -984, 329, 775, 560, -715, 1327, -983, -2216, -34, 353,
  -310, -8, -231, 277, 581, -509, 842, -1678, 980, -67, -124, 629, 897, 543,
  524, -2041, -698, 435, 857, -101, 382, 287, 579, 265, -1029, -104, 539,
  -934, 562, -312, 2086, 792, -790, 748, 421, -1179, 2051, -1092, -482,
  -1232, -945, -313, 1110, 1870, 710, -682, -1103, 123, -312, 161, -214,
  -783, -292, 325, -355, -934, 777, -1937, 686, 1337, 378, -650, 1220, -878,
  -79, -1501, 1732, 375, 417, -402, -309, 1962, -1002, 1578, -1528, 128,
  174, 1669, -223, 2447, 0, 379, 586, 636, -1858, 838, -136, 326, 771, 1619,
  179, -406, 507, 2459, -341, 2719, -649, 1718, -3611, -1611, 252, 818, 592]

theorem fractionalNearFrameSubtreeG2R0226_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0226Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0226Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0226Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0226_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0226LowerBoundTable : List ℤ :=
  [-364, 2134, 245, 631, -75, 33, 514, 33, -536, 4042, 2800, -1016, 102,
  580, 1846, 2542, -2155, 4600, 2139, 1639, 1891, 655, 2394, -2821, 5223]

def fractionalNearFrameSubtreeG2R0226LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0226Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0226LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
