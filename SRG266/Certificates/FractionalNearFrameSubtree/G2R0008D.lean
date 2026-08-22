import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0008`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0008Mask : ℕ := 262424520278097

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0008Witness : Array ℤ :=
  #[-82, 485, -86, -229, 594, -670, 874, 1078, 717, 2286, 1331, 583, -424,
  -1358, -905, -1523, -789, -1397, 395, 0, 185, -352, 57, -1082, -645, -97,
  -474, 471, 714, 898, 337, 125, 875, 416, 384, 441, 43, 924, -289, -477,
  -933, 808, -22, 0, 236, -934, 405, -97, 534, 718, 427, 1039, -427, 971,
  -669, -515, 402, -673, 576, -134, 931, 46, -376, -389, 20, -3, -591, -857,
  -50, 619, -88, 12, -145, 158, 361, 165, 129, -268, 408, 127, 114, 121,
  -492, -97, 134, 355, 328, -212, 193, -391, 192, 376, 40, -256, 224, -858,
  -1200, 537, 490, 54, 634, -74, -606, 453, 138, 311, 29, -363, -763, -179,
  -234, -1131, 1383, 694, 240, -75, 1622, 0, -315, 653, -127, -357, -590,
  -323, -85, 1188, -47, 127, 320, -542, 171, -180, 459, 85, -119, 767, -491,
  264, -134, 619, -12, -424, -199, -194, 257, -70, -173, -199, -34, -229,
  -108, 66, -325, 573, 244, 596, 1041, 609, 334, 620, 1450, 975, -200, 1282,
  927, -89, -147, 80]

theorem fractionalNearFrameSubtreeG2R0008_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0008Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0008Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0008Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0008_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0008LowerBoundTable : List ℤ :=
  [418, 1509, 1272, 58, 33, 1434, 1140, 1398, 1239, 98, 1621, 4137, 1033,
  94, 3255, 1760, 1370, 101, 4368, 1967, 713, -2025, 1862, 1527, 101]

def fractionalNearFrameSubtreeG2R0008LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0008Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0008LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
