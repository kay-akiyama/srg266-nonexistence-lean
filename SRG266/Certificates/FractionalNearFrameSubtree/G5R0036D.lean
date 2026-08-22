import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0036`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0036Mask : ℕ := 1593453573022723

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0036Witness : Array ℤ :=
  #[1088, 304, 163, 323, -294, -364, 43, 0, -768, -1102, -976, 573, 245,
  1279, 20, 828, 518, 514, 767, -348, 317, -360, 222, 386, 370, -846, 169,
  -93, -410, 737, -80, -591, 413, 0, 143, -145, -260, 978, 984, -603, -810,
  -934, -1022, 48, 305, -13, -410, 21, 27, -213, 413, -822, -560, 638, 617,
  -508, -488, -30, 186, 415, 600, -307, -468, 465, 467, 160, -965, -263,
  -501, 1298, 150, -185, -1142, 322, -467, -344, 426, -294, 1089, -837, 851,
  734, -373, -578, 376, -305, 184, 28, -508, -245, 1279, 55, -679, 566, 461,
  -793, 299, -245, 431, 753, 119, -180, 433, -540, -342, -1009, -317, 792,
  335, 512, 587, 306, -246, 609, 728, 516, -192, 3, -134, -168, -1042, -376,
  500, -49, -691, -352, 458, 310, -219, 52, 10, -53, 360, 78, -581, 77, 448,
  44, 513, -63, 512, -569, -308, -225, -25, -635, 805, 907, 535, 12, -517,
  -227, -673, -330, -980, 137, -148, -464, 63, -1001, 38, 48, 390, -320,
  -858, -814, 0, 498]

theorem fractionalNearFrameSubtreeG5R0036_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0036Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0036Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0036Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0036_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0036LowerBoundTable : List ℤ :=
  [-682, -872, -1353, 715, 31, 12, -900, 1113, 1557, 213, -2217, 99, 651,
  2440, 99, 515, 391, -1141, -2563, 1850, -2411, 2310, 2689, -1993, 1517]

def fractionalNearFrameSubtreeG5R0036LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0036Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0036LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
