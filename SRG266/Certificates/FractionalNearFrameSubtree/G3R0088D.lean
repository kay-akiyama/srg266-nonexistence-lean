import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0088`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0088Mask : ℕ := 2503858713380358

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0088Witness : Array ℤ :=
  #[129, -79, 6, -151, 143, 14, 323, 0, 389, 73, 386, -351, -251, -276, -35,
  -204, -19, -212, 34, 1, -74, 6, 40, -8, 105, -118, 23, 0, 423, 3, 395,
  -55, 465, 30, -30, -28, 15, -48, 57, -200, -27, -57, 115, 0, -81, -109,
  94, -24, 206, -207, -246, -98, 172, 40, 237, 135, 256, 0, 323, 55, 153,
  -524, -336, -325, -19, 38, -236, -173, 66, 80, -50, 123, 189, 253, -117,
  309, -61, -293, -39, 81, 242, 50, 89, 213, 193, 106, 313, 106, -239, -37,
  -174, 133, 69, 40, -222, 173, -206, 70, -56, -99, -92, 100, 102, 68, 36,
  39, 23, -114, 272, -110, 45, -133, -5, 146, 44, -205, 109, 351, 60, 166,
  -32, -285, 86, -121, 206, 127, 175, -346, 147, 210, 247, -309, 361, 10,
  146, 95, 192, -20, 366, -28, 173, -45, -40, -61, -65, 125, -230, 296, -15,
  237, -35, 243, 436, 47, 48, 150, 145, 106, -98, 0, 32, -36, -214, -61,
  -343, 420, 216, -3]

theorem fractionalNearFrameSubtreeG3R0088_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0088Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0088Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0088Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0088_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0088LowerBoundTable : List ℤ :=
  [162, 467, 405, 444, 430, 205, 153, 2, 414, 55, 491, 1097, 803, 586, 843,
  376, 10, 909, 671, 250, 591, -240, 302, 224, 639]

def fractionalNearFrameSubtreeG3R0088LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0088Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0088LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
