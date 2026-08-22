import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0117`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0117Mask : ℕ := 1310250322862177

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0117Witness : Array ℤ :=
  #[-73, 132, 609, 559, 175, 555, -1439, -745, -950, -723, -962, 225, 24,
  537, -569, 26, 0, 47, 232, 778, -87, 99, 276, -779, -547, 51, -321, -783,
  402, -24, -404, 1044, 415, 15, 1093, 739, 124, -354, 0, -496, 206, -802,
  -958, -744, 195, 731, 449, -287, -378, 0, -477, 588, -399, 55, 602, 159,
  -618, -916, 844, 560, -26, -523, 281, 220, 231, 20, 102, -345, 651, -796,
  -1301, 483, 770, 514, -521, 664, -105, -315, 177, -447, 433, 134, -28, 94,
  -65, -545, -273, -1192, 657, -861, 248, -624, -687, 38, 473, 403, 409,
  748, 191, 1220, 1041, -171, -22, -126, 647, 689, 449, 520, -224, 165, 405,
  -148, 1005, 506, 622, 898, 528, 928, -412, 108, 112, 419, -348, 744, 97,
  925, 381, -12, 300, 200, -51, -875, 79, 599, 284, 387, 345, -465, 993,
  812, 458, -466, 511, 544, 336, 303, 1372, 632, 433, -343, 192, 391, 366,
  223, -239, 178, 337, 39, -532, -544, 459, -21, 129, -237, 94, 685, 319,
  -1517]

theorem fractionalNearFrameSubtreeG2R0117_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0117Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0117Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0117Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0117_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0117LowerBoundTable : List ℤ :=
  [356, 3037, 543, 992, 31, 1160, 31, 32, 227, 1789, 3102, 1687, 4590, 1230,
  440, 2660, 2582, 99, 1892, 2005, 1066, 158, 516, 100, 3368]

def fractionalNearFrameSubtreeG2R0117LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0117Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0117LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
