import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0337`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0337Mask : ℕ := 5644740981928969

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0337Witness : Array ℤ :=
  #[30, 249, 56, 192, 82, 83, 0, 8, -50, -26, -42, -39, 7, -145, 63, 129, 0,
  -63, 27, 133, 7, -25, -11, 15, 40, -52, -4, -58, 194, 98, 66, 150, 66,
  115, 5, -37, 42, 42, 94, -55, -18, -117, 79, -68, 195, -23, 43, 99, -55,
  -1, 101, 43, 45, 68, 131, 61, 116, 93, 225, -171, 66, 15, 50, -68, -52,
  74, 31, -64, -55, -148, -10, -18, -11, -27, 0, 35, 133, -13, 134, -1, -46,
  37, 34, 61, -42, 48, 113, -59, -60, -56, -14, -27, -4, -71, -118, 132, 63,
  -34, 46, 24, 5, 125, -80, -41, 117, 86, -64, 125, -27, 80, 76, 42, 46, 32,
  28, -9, 73, 24, 131, 103, -142, -11, -142, 90, -58, 66, 110, 51, 127, 122,
  2, 12, -7, 52, 164, -4, 37, -11, 178, -92, -50, 163, -28, -15, -46, 2, 43,
  148, -50, -32, 157, 43, -70, -137, -66, -17, -157, -157, 8, -50, 36, 3,
  25, -61, 2, 40, -28, -12]

theorem fractionalNearFrameSubtreeG2R0337_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0337Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0337Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0337Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0337_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0337LowerBoundTable : List ℤ :=
  [184, 97, 185, 156, 215, 424, 325, 311, 315, 302, 281, 219, 178, 9, 65,
  508, 190, 106, 233, 10, 319, 10, 667, 310, 486]

def fractionalNearFrameSubtreeG2R0337LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0337Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0337LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
