import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0526`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0526Mask : ℕ := 6780114529145361

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0526Witness : Array ℤ :=
  #[-874, -1200, -817, -1712, -2332, 0, -645, 1037, 379, 828, 1204, 340,
  -595, 1042, 717, 224, 989, 2530, 714, 587, 238, -341, 785, 361, 517, 908,
  506, 447, -483, -898, -331, 39, -166, 264, 69, -638, 196, 429, 88, 528,
  82, 475, 732, 486, -527, 40, 565, -471, 26, 31, -793, -5, 164, 168, 400,
  761, 759, 462, 657, 435, -66, 2, 51, 355, 678, -407, -299, -1036, -534,
  -385, 37, -349, -229, 314, -603, 742, 461, -86, -804, 886, 932, -229, 795,
  -1034, 912, 325, 45, 529, 331, 601, 181, 1193, -597, -10, 125, 1394, 13,
  -109, -469, -302, -595, -622, 322, -593, -270, -1620, -670, -447, 124,
  -1704, -864, 98, -248, 1658, 166, 0, 301, 268, 265, -145, 1617, 412, -381,
  103, -60, 364, 488, 511, 330, 101, 208, 660, -115, -159, -706, -85, 87,
  -412, 564, -249, 568, -204, 255, -111, 576, -384, 877, 777, -453, -1094,
  206, -70, 1385, 418, -384, 205, 431, -212, 452, 47, 43, -388, -67, -288,
  -736, -2059, 198, -428]

theorem fractionalNearFrameSubtreeG2R0526_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0526Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0526Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0526Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0526_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0526LowerBoundTable : List ℤ :=
  [299, 33, 32, 1847, 1324, 1831, 28, 34, 655, 397, 1767, 393, 708, 345,
  2010, -234, 1228, 774, 1173, -550, 4365, 100, 2400, 1434, 988]

def fractionalNearFrameSubtreeG2R0526LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0526Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0526LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
