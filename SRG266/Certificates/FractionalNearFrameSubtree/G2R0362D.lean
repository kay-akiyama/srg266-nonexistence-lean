import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0362`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0362Mask : ℕ := 5713997271245962

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0362Witness : Array ℤ :=
  #[419, -146, 164, 320, -204, -651, 932, 0, 311, 549, 0, 527, 380, 241,
  172, -707, 759, 590, 461, 575, 417, 503, -453, -362, 64, -73, 332, -358,
  -527, -1112, 53, 104, -584, 610, -305, 138, 297, -14, 237, -600, -74, 0,
  -263, 219, -103, 613, -588, 185, 167, -49, -343, 66, -387, 159, -166,
  -248, 773, 109, 658, 71, 26, 108, -213, -229, 109, -144, -199, -94, 6,
  -496, -111, 40, 23, 240, 377, 162, 234, 514, 272, -289, 192, -934, 351,
  -505, -63, 0, -447, -209, -33, -556, -398, 213, 901, 423, 198, 279, 471,
  -6, 48, -502, 28, 468, -273, 400, 4, -653, 32, -186, 444, -51, 800, 647,
  -209, -875, 97, -935, 722, -412, -139, -499, -491, -648, 707, -138, 201,
  -107, 650, 139, 623, 643, -842, -287, 294, 139, 855, 202, 452, 353, 209,
  -66, -288, 227, -201, -8, -255, 316, 347, -69, 140, 295, 270, -219, -993,
  -223, 182, -655, -28, 48, 513, -100, 47, -973, 60, -151, 670, 672, 1422,
  -33]

theorem fractionalNearFrameSubtreeG2R0362_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0362Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0362Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0362Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0362_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0362LowerBoundTable : List ℤ :=
  [-396, 593, -47, -379, 379, 872, 1042, 1764, 1386, 3208, 1109, 99, 1155,
  128, 934, -95, 100, -623, 832, 1096, -1297, -693, 665, -779, 1861]

def fractionalNearFrameSubtreeG2R0362LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0362Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0362LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
