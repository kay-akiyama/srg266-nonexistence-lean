import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0341`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0341Mask : ℕ := 5645826728238097

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0341Witness : Array ℤ :=
  #[739, 353, 1550, 684, 1517, 76, 1243, 1002, 2061, 1707, 3634, 1502,
  -2378, -4238, -1525, -1144, -2128, -3284, -852, -1224, -1047, 163, -97,
  -1629, -856, -811, -360, 1142, 1060, 1266, 2210, 2912, 1367, 277, 928,
  1762, 1939, -1320, -1135, -492, 694, -673, 1201, -69, -95, -490, -612, -4,
  -314, 509, -185, -915, 2083, -266, 217, 489, -1049, 508, 341, -599, 358,
  -580, -1, 501, 601, 467, 352, 213, -364, -373, 63, -145, -382, 250, 719,
  891, 145, -371, -449, 257, -975, -936, -284, -52, 1245, 769, 637, 605,
  278, -2, 303, -837, 230, 829, 1253, 1084, -272, 46, -651, -258, 793, 331,
  238, 1402, 1076, 458, 792, 315, 186, 1326, 0, 707, -1116, 1066, 610, -360,
  2041, -1682, 1033, 261, 113, 230, -190, 135, -311, 964, 1710, -233, -1746,
  -123, 112, -399, 470, 32, 42, 985, -223, 94, -67, -379, 750, 234, 886,
  -214, -365, -110, -767, 827, -28, 257, -565, 597, 477, 1283, -100, -4,
  401, 234, -2110, 204, 653, 178, 626, -1116, 601, 1721, 1003, -1332]

theorem fractionalNearFrameSubtreeG2R0341_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0341Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0341Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0341Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0341_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0341LowerBoundTable : List ℤ :=
  [1585, 1823, 2319, -128, 3600, 1302, 31, 4319, 32, 5035, -1211, 4881, 100,
  5319, 4124, 4176, 3843, 3586, -610, -1085, 1199, 4117, 2827, -1919, 5799]

def fractionalNearFrameSubtreeG2R0341LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0341Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0341LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
