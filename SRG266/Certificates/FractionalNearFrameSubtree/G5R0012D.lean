import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0012`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0012Mask : ℕ := 936563095601219

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0012Witness : Array ℤ :=
  #[40, -131, 317, -192, 6, -528, 95, 74, 133, 313, 565, -278, -476, 46,
  -163, -26, -10, 86, 42, 287, -41, -427, -30, -499, -261, -261, -10, 82,
  63, 404, -338, 297, 228, 383, 341, 239, 100, -112, 2, 7, -166, -103, 166,
  196, -39, 0, -449, 0, -549, 113, 114, 38, 238, 0, -90, 308, 21, 28, 96,
  117, 47, 411, -231, -227, 496, -43, 248, 392, -283, 27, 210, -103, 550,
  -112, 95, 205, -382, -41, 145, -147, -241, -89, 180, -340, -401, 68, 110,
  260, 151, -171, 391, -73, -139, -176, 6, 359, 81, 136, 116, 384, 490, 75,
  428, 253, 232, -122, -141, -145, 278, -399, -513, -357, 205, -54, -328,
  -276, -178, -14, 95, 209, 86, -319, -114, 134, -2, 62, 453, 4, -185, -48,
  -157, 45, -450, -170, -26, 30, -203, 528, 93, 314, 193, -276, -242, -309,
  -22, -134, -232, -110, -288, -208, 5, -80, 173, -71, 118, 101, 185, 221,
  517, -16, 122, 145, 1090, -129, 130, 34, 60, -424]

theorem fractionalNearFrameSubtreeG5R0012_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0012Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0012Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0012Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0012_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0012LowerBoundTable : List ℤ :=
  [-205, 2, 1255, -734, 112, 1, 672, 37, 1, -826, 903, 5, -457, 6, 349,
  1128, 869, 10, -409, 408, 353, 1732, -291, 285, 651]

def fractionalNearFrameSubtreeG5R0012LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0012Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0012LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
