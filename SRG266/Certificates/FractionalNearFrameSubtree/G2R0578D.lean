import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0578`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0578Mask : ℕ := 6850589767602788

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0578Witness : Array ℤ :=
  #[-825, -236, -218, -642, 142, 374, -655, -468, -287, 118, 76, 513, 576,
  833, 542, 549, 3, 229, 708, 344, 361, 763, -167, 113, 235, 514, -703,
  -165, -1467, -373, -483, -486, -869, -269, 324, 565, 12, 283, -285, 472,
  792, 729, -340, -409, 696, 146, -510, -223, -158, 468, -741, -1075, 524,
  419, 126, 1066, -127, 209, -1006, 34, 503, 249, -568, -443, 23, -448, 453,
  361, -647, -251, 248, -122, 280, 205, -398, 524, -294, 614, -17, 368,
  -206, 474, 50, -126, 308, -610, 217, 221, 1268, -27, 309, 134, 317, 220,
  273, 272, -367, -157, 904, -203, 278, -105, -25, -921, 267, 1119, 614, 0,
  -289, 121, -105, 304, -661, -744, -293, -582, -1181, -122, -401, 402, 139,
  993, 471, -778, 51, 420, 478, -176, 23, -666, 289, 462, -393, -111, -103,
  583, -39, 239, -810, 347, -598, 472, 924, -203, -325, 102, 766, -849,
  -364, -68, 30, 371, 372, -74, -454, -185, 303, 523, 92, 355, -546, -261,
  -681, 513, -702, 757, -270, 466]

theorem fractionalNearFrameSubtreeG2R0578_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0578Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0578Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0578Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0578_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0578LowerBoundTable : List ℤ :=
  [-24, 33, 32, 815, 354, -26, 453, 204, 33, 761, 385, 189, -606, 1738, 100,
  -781, 2439, 810, 964, 2252, -161, 980, 101, 100, 99]

def fractionalNearFrameSubtreeG2R0578LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0578Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0578LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
