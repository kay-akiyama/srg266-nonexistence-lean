import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0355`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0355Mask : ℕ := 5671103491191073

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0355Witness : Array ℤ :=
  #[-51, 99, 83, 0, -51, 8, 0, 256, 245, 93, 248, 159, -415, -382, -136,
  -31, -198, -181, -184, -502, 63, -164, -80, 37, -42, -71, 76, -10, 185,
  107, 357, 334, 84, 20, -34, -291, 112, 93, 0, -81, 313, -17, 31, -23,
  -238, -124, 103, -133, -98, -267, 66, 231, 112, 172, 130, 39, -176, 140,
  212, 160, 217, -409, -150, -37, 110, -313, -247, 67, 58, -76, 39, -90,
  -204, 190, 28, 131, 64, -78, 99, -109, -64, -44, 28, -15, -62, 114, 42,
  80, 161, 148, -127, 149, 23, 113, -22, -28, 19, 94, -91, 56, 134, 105,
  -113, -12, 151, 162, 181, 128, 52, -169, -17, 1, 66, -99, 30, 184, 219,
  126, 22, 11, -182, 0, 255, 230, 13, -65, -218, 159, -63, 45, 11, -42, -28,
  -97, 48, 102, -37, 110, 57, -151, 46, 204, 196, 147, 5, 118, 16, -76, 35,
  -143, 43, 93, 48, -73, 223, 35, -65, -20, 3, 141, -31, -65, -116, 36, 4,
  12, 149, -99]

theorem fractionalNearFrameSubtreeG2R0355_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0355Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0355Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0355Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0355_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0355LowerBoundTable : List ℤ :=
  [-21, 270, 118, 10, 364, -78, 1, 240, 2, 10, 564, 81, 46, -424, 402, 629,
  895, -125, 10, 466, 35, 758, 648, 358, 429]

def fractionalNearFrameSubtreeG2R0355LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0355Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0355LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
