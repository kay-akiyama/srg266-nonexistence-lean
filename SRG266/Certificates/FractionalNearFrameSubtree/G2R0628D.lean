import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0628`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0628Mask : ℕ := 11298250674870817

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0628Witness : Array ℤ :=
  #[338, 43, 631, 625, 450, 59, -625, 55, -720, -126, 0, -484, 601, 233, 83,
  468, 867, -286, 295, 398, 420, 340, 530, 166, 263, 451, 34, -160, -181,
  -221, -1149, 558, -3, -271, 937, 391, -144, -130, 388, 0, -62, -446, 126,
  -575, 1083, 145, 13, -113, 36, 84, -376, -55, -161, 345, -314, -196, 574,
  -178, -6, -43, 310, 232, -639, -45, -45, 417, -379, 798, -758, -85, -92,
  155, 64, 303, 239, -112, -313, -108, 26, -160, 66, 188, -140, 147, -84,
  441, -138, 155, -607, 3, 190, -279, 142, 67, 53, 188, 105, -204, -698,
  -271, 193, -118, 341, 4, 206, -36, 531, 164, -727, 113, 82, 441, 73, -54,
  409, 438, 416, 298, -881, 958, -51, -215, 17, -283, 588, -104, 393, -410,
  -136, -343, -11, 5, 426, -92, -202, -227, -94, 183, 751, -225, -440, -145,
  -118, -144, 321, 160, 46, 181, 157, 370, 256, 194, -135, -205, 329, -4,
  125, -95, 474, -420, -57, -218, 425, -76, 149, -263, 719, -587]

theorem fractionalNearFrameSubtreeG2R0628_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0628Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0628Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0628Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0628_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0628LowerBoundTable : List ℤ :=
  [440, 474, 33, 32, 1848, 32, 719, 940, 1215, 1214, 100, 1814, -500, 1087,
  1859, 884, 632, 203, -147, 704, -206, 1107, 377, 102, -7]

def fractionalNearFrameSubtreeG2R0628LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0628Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0628LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
