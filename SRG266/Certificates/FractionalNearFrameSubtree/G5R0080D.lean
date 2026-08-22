import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0080`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0080Mask : ℕ := 5439062944686482

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0080Witness : Array ℤ :=
  #[240, -297, 541, 499, -421, 481, -13, 143, -12, -32, 888, 545, -425, 182,
  -405, 71, -320, -857, 488, 544, -302, 388, 7, -48, 370, 170, 319, -341,
  1020, 569, 0, -299, 298, -526, -357, -623, 566, 111, -417, -556, -278,
  344, 381, 87, 837, -470, -50, 284, -744, -541, 519, 393, 1108, 565, 967,
  475, 498, 845, 1350, 530, 18, -832, -199, 443, -817, -38, -328, -563, 712,
  655, -488, -218, 897, -713, 75, -558, 465, -355, 185, 60, 148, 455, -109,
  -632, -115, -604, 152, -130, -499, 359, 705, 736, 722, 972, 660, -172,
  -634, 484, 156, 643, -833, 398, -272, 675, 111, 879, 16, -468, 527, -455,
  -9, -438, -303, 402, 332, -635, -24, -650, 190, 722, 742, 412, 943, 917,
  -222, 427, 811, -175, 78, 232, -524, -67, -809, -439, 872, -685, 5, 643,
  -730, 416, 438, 327, 322, 552, 38, -35, -602, 237, 1326, -14, -411, 310,
  -434, -686, -615, 447, -212, -60, 421, -686, 0, -555, 184, 247, 417, 258,
  -1404, -309]

theorem fractionalNearFrameSubtreeG5R0080_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0080Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0080Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0080Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0080_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0080LowerBoundTable : List ℤ :=
  [278, -27, 519, 2224, 33, 2304, 596, 31, 1244, 100, 2278, 3309, 100, 2069,
  823, 2779, 760, 3425, 2940, 1788, -900, 365, 1420, 98, 100]

def fractionalNearFrameSubtreeG5R0080LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0080Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0080LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
