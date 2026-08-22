import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0189`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0189Mask : ℕ := 1393645772542184

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0189Witness : Array ℤ :=
  #[194, 352, 618, 297, -136, 508, 274, 795, 54, 180, -829, -482, -592, 175,
  148, 24, -659, 405, -373, 527, 407, 760, -4, -474, -107, -1581, 30, 413,
  82, 258, 877, -18, 168, 100, -348, -733, -431, 288, 117, -234, -72, -605,
  -759, 257, -268, 8, 430, -120, 288, 66, 625, 331, 47, -413, -540, -305,
  -534, 102, 447, 185, 894, 664, 470, -671, 465, 581, 555, 770, -299, 530,
  189, 902, 240, -570, 630, 14, 248, -634, 799, -139, -1674, -449, 345, 352,
  -631, 473, 72, 178, -810, 690, -29, 378, -627, 497, -416, 526, 289, 46,
  -371, 104, -201, 842, -930, 369, -32, -1, 135, -41, -715, -536, 858, -204,
  -62, -709, -321, -410, -498, -211, -371, -755, 601, -290, -378, -97, -95,
  -100, -87, -702, -145, 422, -383, -873, -576, 521, 378, -426, 590, -349,
  593, -136, -1022, 1426, 103, -1622, -1318, 1106, 230, -68, -312, 388, 930,
  166, 247, -69, 452, 291, -816, 205, -96, 441, 1031, 322, 828, 285, 530,
  -10, 121, -388]

theorem fractionalNearFrameSubtreeG2R0189_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0189Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0189Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0189Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0189_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0189LowerBoundTable : List ℤ :=
  [-496, 31, 32, 1057, -82, 476, 31, 31, 42, 1372, -2507, 640, -1675, 207,
  -586, -1052, 959, 653, 702, 1661, 2539, 1711, 1424, 1606, 101]

def fractionalNearFrameSubtreeG2R0189LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0189Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0189LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
