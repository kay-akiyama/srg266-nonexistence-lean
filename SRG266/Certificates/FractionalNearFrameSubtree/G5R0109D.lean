import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0109`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0109Mask : ℕ := 5792008559303697

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0109Witness : Array ℤ :=
  #[-266, -197, -283, 370, 225, 94, -317, -562, -116, 1, 174, 294, 52, 392,
  397, 230, 285, -95, 177, -77, 699, 157, 604, -156, 205, 593, -824, -260,
  -705, -115, -125, -230, -438, -126, -66, -714, 360, 787, 620, -103, -367,
  -199, 354, 77, -70, -104, -8, 188, 176, 219, -238, 160, 2, -292, 437, 101,
  -219, 84, 21, -143, 145, 245, 10, 39, -43, 197, 18, -334, 489, 262, 551,
  347, 168, 210, 39, 204, 284, -254, 380, 82, -143, -611, -321, -122, -18,
  0, -588, 305, 189, -106, -34, -66, -45, 276, 113, -213, -295, 371, -72,
  383, -364, 6, 0, 59, -196, 1, 135, -294, -281, -101, 389, 249, -141, -36,
  -194, 323, 348, 186, 498, -421, -696, -504, -28, 666, -293, -2, 186, 49,
  -34, 47, 90, -135, -564, -627, 59, 329, -152, 607, -229, 47, 86, 57, 372,
  -16, -71, -183, 186, 135, -606, -94, -375, 277, -392, 92, 89, 572, -127,
  169, 199, -22, -40, 76, 268, 2, -219, 304, 227, 52]

theorem fractionalNearFrameSubtreeG5R0109_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0109Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0109Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0109Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0109_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0109LowerBoundTable : List ℤ :=
  [-49, 32, 32, 233, 1148, -141, 32, 27, 362, 50, -978, -328, 2242, 366,
  -598, -474, 1196, 1416, 119, 459, 1828, 1467, 812, 100, -658]

def fractionalNearFrameSubtreeG5R0109LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0109Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0109LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
