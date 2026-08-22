import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0090`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0090Mask : ℕ := 5508334370786578

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0090Witness : Array ℤ :=
  #[8, 193, 100, -541, 98, -420, 783, -75, 683, 197, -139, -485, 288, 2,
  -648, -657, -165, -40, -273, -33, -90, -86, 809, 3, 418, -60, -181, 99,
  -1553, 152, 518, 10, -246, 558, 679, 174, -517, 118, 642, -2, 581, -172,
  -294, -367, -496, 540, -135, 67, 567, 259, 412, 314, -473, 59, 48, -200,
  69, -552, 14, 12, 882, 698, 78, 1049, -499, -315, 392, -451, 585, 242,
  -345, 413, 1171, 392, -101, -64, 448, 39, 167, 915, 367, 490, -72, 17,
  -161, -223, 242, -270, 371, 336, 486, 152, 101, -190, 186, 272, 88, 409,
  323, -797, 356, 0, -18, 41, 513, 631, -229, -901, 17, 489, 677, 367, -107,
  -627, -590, -527, -36, -305, 420, -404, -92, -164, 504, 321, 34, -718, 12,
  389, 107, -717, 829, 127, 401, 0, 83, -185, -844, 55, -520, -113, -65, 60,
  -431, -130, 597, 141, 500, 9, 235, 278, -423, -578, -83, 454, 390, -946,
  392, -58, 497, 947, 146, 925, 912, 205, 1060, 258, 138, 831]

theorem fractionalNearFrameSubtreeG5R0090_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0090Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0090Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0090Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0090_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0090LowerBoundTable : List ℤ :=
  [521, 864, 1975, 306, 605, 32, 179, 1229, 825, 2869, -592, 1908, 1342,
  2441, 100, 2245, 6336, 759, 613, 100, 100, 3017, 871, 1433, 1204]

def fractionalNearFrameSubtreeG5R0090LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0090Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0090LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
