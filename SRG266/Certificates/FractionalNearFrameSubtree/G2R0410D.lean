import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0410`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0410Mask : ℕ := 5742495572302256

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0410Witness : Array ℤ :=
  #[1027, 82, 1056, 251, 581, -582, 668, -647, -217, -352, 498, 208, -37,
  -910, 859, 46, -55, 83, -118, -644, 1175, -810, -103, -351, 968, 1030,
  -150, -959, -342, -1033, 219, 351, 559, 2000, 577, 37, -464, -442, 338,
  539, -793, 809, -544, 409, -843, 424, 546, 501, 187, 665, 649, 291, 152,
  -139, -534, -899, 2707, 932, -72, 1234, -394, 661, -593, 345, -736, 359,
  395, 20, -338, 2138, -724, 991, 591, -990, 151, 248, -408, -235, 757,
  -788, 961, 258, -631, -236, 1232, -853, 202, -1535, 1853, -204, -91, -664,
  889, 769, -132, 154, 929, 391, 229, -501, -186, 639, 630, 787, 680, 336,
  -10, 76, 134, 31, -812, -175, -908, -1032, -1676, 2185, 2015, 913, 1833,
  1612, -749, 110, -499, 217, 169, -897, -969, -1058, 73, -320, -513, 279,
  -322, 15, 1342, -626, 557, -236, -419, 456, -532, 118, 861, 1472, -1440,
  -807, 553, 11, 790, -659, 729, 747, 585, -91, 753, -711, 377, 1492, -992,
  318, 42, 63, -307, -834, 905, 1009, 1196, 405]

theorem fractionalNearFrameSubtreeG2R0410_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0410Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0410Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0410Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0410_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0410LowerBoundTable : List ℤ :=
  [885, 1515, 919, -444, 3646, 1997, 32, 2679, 2849, 3150, 315, 3601, -533,
  6771, 2631, 100, 101, 2801, 1696, 651, 1446, 3314, 2860, 1707, 4175]

def fractionalNearFrameSubtreeG2R0410LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0410Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0410LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
