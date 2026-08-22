import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0184`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0184Mask : ℕ := 6866160432620194

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0184Witness : Array ℤ :=
  #[212, 78, 145, 30, 110, 35, 80, 131, -91, 66, 89, 169, -256, -26, 0, -14,
  -108, -85, -16, -83, 144, 175, 136, 168, 5, -157, -3, -204, 210, 316, 40,
  93, -345, -116, -231, 159, 80, 257, 149, -29, 78, -46, -122, -295, -474,
  68, 258, 29, -16, 206, 269, 159, -138, 23, -83, -270, -381, 129, -120,
  142, 0, -149, 345, -58, 118, -91, 176, -10, -242, 112, 15, 70, 91, 198,
  179, -88, -108, 269, 172, -92, 137, 102, -88, -175, 128, 172, 42, -154,
  74, 37, 98, 125, -153, -6, -175, 49, -224, -118, 322, 200, 258, -105,
  -139, 43, 223, 318, 291, 392, 150, 305, -187, 260, 376, 192, -136, 0, 177,
  -21, 348, -289, -17, 128, 107, -76, 44, 419, 115, -459, -104, 231, -207,
  -263, -152, -36, 187, 55, 155, 83, 39, 161, 77, 121, -230, -131, 44, -111,
  -112, 27, 52, 156, 108, -42, -39, 50, -106, 184, 52, 247, 270, -247, 372,
  38, 119, -84, -108, -85, 85, -304]

theorem fractionalNearFrameSubtreeG3R0184_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0184Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0184Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0184Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0184_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0184LowerBoundTable : List ℤ :=
  [193, 376, 61, 282, 213, 418, 417, 392, 350, 639, 118, 1424, 420, -500,
  159, 544, 1038, 371, 839, 1115, 119, 527, 10, 716, 461]

def fractionalNearFrameSubtreeG3R0184LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0184Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0184LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
