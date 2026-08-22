import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0378`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0378Mask : ℕ := 5738055651272202

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0378Witness : Array ℤ :=
  #[774, 380, 426, 480, 398, 497, -852, -915, 248, -326, -215, 145, 726,
  -351, -206, 144, -420, 261, 848, -360, -69, -417, -461, 269, 427, -149,
  -407, 106, 233, 242, -337, -419, -503, 2372, 424, 937, -360, -403, 38, 41,
  392, -379, 555, 7, -651, 2061, 17, 11, -218, 511, -108, -538, 86, -406,
  1146, 1097, 291, -891, 681, 427, -319, -540, -1322, 1006, 204, -1382,
  -1862, 736, -1311, 789, 180, -295, 24, -706, 492, 156, -390, 0, 967, 1847,
  -87, 17, 584, -821, 773, -950, 291, 238, 717, 339, 471, 568, -142, 123,
  -169, 1748, -135, -61, -44, 697, -673, 78, 179, 18, 299, -1321, -239,
  -887, -535, 1195, 2179, 1488, -1279, -2065, -1796, -572, 29, -1063, -1549,
  198, -1267, -159, 1054, 2197, 837, -62, -27, 695, -126, 232, 350, -80,
  126, 280, 48, 923, 1186, -163, 163, 537, 50, 0, -385, -754, 529, -132,
  -264, -630, -136, -169, 138, 191, 336, 183, 197, -95, -64, -104, -550,
  -870, -413, -482, -101, -452, -179, -74, 140, 427]

theorem fractionalNearFrameSubtreeG2R0378_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0378Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0378Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0378Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0378_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0378LowerBoundTable : List ℤ :=
  [-114, -1099, -368, 1519, 33, 32, 2346, 1359, -882, 60, 100, 4323, -3792,
  1203, 983, -1492, -1329, 2210, 347, 1659, 1741, 5001, -1299, 2235, 1732]

def fractionalNearFrameSubtreeG2R0378LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0378Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0378LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
