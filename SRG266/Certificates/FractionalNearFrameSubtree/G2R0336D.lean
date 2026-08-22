import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0336`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0336Mask : ℕ := 5644725094390281

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0336Witness : Array ℤ :=
  #[-1119, -927, -749, -932, -1419, -972, 229, 0, -35, 268, 107, -467, 1305,
  1226, 946, 1168, 651, 1362, 1104, 632, 575, 769, 635, -376, 141, -36, 173,
  -244, -455, -365, -1021, -7, 446, 433, 85, 21, -608, 604, -94, -446, 392,
  226, -107, -497, 608, -289, 119, -84, 496, 263, 72, 25, 596, 151, 137,
  -84, -112, 267, 18, -151, 520, 555, 0, -339, -74, 755, 219, 79, 792, 233,
  -216, 201, 290, -254, 325, 74, 636, -94, 102, 327, -319, 384, -106, -147,
  65, -394, 500, -407, 281, 691, 415, -742, 121, -63, -251, 685, 344, 767,
  702, 161, 187, -4, -253, -153, 183, -146, -95, 279, -203, -14, -908, 50,
  -353, -116, -444, -320, -178, 1246, 378, 606, -397, 168, -335, -304, 452,
  148, -368, -156, 137, 32, 529, 70, 277, 18, 141, 304, 215, -110, 28, 415,
  -80, -263, 290, -108, 377, -108, -69, 103, 153, 221, -198, 605, 127, -25,
  -428, -72, -326, -509, 479, -266, -202, -181, -281, -522, 200, 65, 339,
  -234]

theorem fractionalNearFrameSubtreeG2R0336_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0336Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0336Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0336Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0336_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0336LowerBoundTable : List ℤ :=
  [503, 60, 1073, 540, 369, 1456, 32, 31, 2558, 3164, 537, 66, 578, 1461,
  100, 476, 2855, 1485, 2186, 98, 2439, -1756, 2862, 1272, -446]

def fractionalNearFrameSubtreeG2R0336LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0336Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0336LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
