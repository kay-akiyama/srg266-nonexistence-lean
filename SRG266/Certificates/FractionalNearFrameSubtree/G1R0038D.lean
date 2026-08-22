import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0038`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0038Mask : ℕ := 537555193414034

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0038Witness : Array ℤ :=
  #[280, 605, 284, -91, 587, -14, 0, 122, -652, 0, -622, -401, 424, 300,
  890, 367, -30, 846, 346, 486, 645, 216, -86, 538, 75, -298, 0, -361, 97,
  105, -445, -216, -840, -128, -368, 16, 326, 116, -247, 48, -23, 316, 216,
  -142, 141, 176, -849, 244, 36, -112, 30, -142, -124, -40, 30, -178, 166,
  -218, -279, -206, 233, 702, 581, 291, -709, 274, 1060, -88, 259, -339, 42,
  97, -447, 177, 79, -121, 53, 278, -146, 90, -221, 196, -198, 340, -85,
  105, -169, -100, 166, 133, -59, 267, -630, 111, 342, -529, 72, 240, 599,
  102, -112, -45, 527, -171, 240, 215, -30, 326, 151, 456, 555, 261, -292,
  -31, -462, 266, 99, -339, -81, -413, 110, -94, 517, 80, 122, 26, -139, 48,
  294, 25, 111, 288, -172, -414, 318, 152, 234, 303, 248, 456, 158, 136,
  -158, 80, -40, 177, 333, -93, -254, 221, 606, 230, -45, -96, 504, 301,
  107, -78, -314, 74, -419, -296, 102, 71, -113, -230, -340, -103]

theorem fractionalNearFrameSubtreeG1R0038_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0038Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0038Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0038Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0038_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0038LowerBoundTable : List ℤ :=
  [508, 377, -106, 1137, 361, 830, 944, 2306, 959, 941, -673, 255, 810,
  -643, 101, 770, 243, 99, 928, 1301, -428, 101, 364, 1781, 2149]

def fractionalNearFrameSubtreeG1R0038LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0038Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0038LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
