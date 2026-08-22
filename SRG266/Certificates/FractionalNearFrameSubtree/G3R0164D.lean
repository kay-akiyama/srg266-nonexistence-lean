import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0164`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0164Mask : ℕ := 6856934331977944

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0164Witness : Array ℤ :=
  #[196, 21, 97, 166, 17, 30, 92, 5, 74, 11, -106, -13, -114, -270, 100,
  -46, 62, 88, -12, 32, -88, 26, -14, -166, 34, 97, 89, -28, 130, 105, 56,
  -26, 117, 76, -260, -64, -230, 39, 82, 232, -78, -118, -2, -5, -140, -13,
  7, 18, 44, 35, 5, 121, 50, 290, 165, 82, 32, -73, -31, 13, -126, 73, 69,
  31, 65, -129, 114, -9, -18, -117, -30, -46, -55, -13, 121, -113, -33, -25,
  -133, -55, 10, 80, -65, 71, -117, -51, 114, -79, -53, 41, 146, -6, 168,
  60, 27, -76, -107, 47, -31, -24, -20, 108, 177, -31, -7, 75, 9, 34, -57,
  40, -59, -104, 36, -98, 91, 68, -47, 63, -5, -168, -7, 89, 95, 83, 91,
  197, 75, -32, 89, -96, -34, 132, -59, 65, -34, 118, 44, -55, 159, -35,
  167, 10, 3, 50, -104, 92, -64, -149, -129, -30, 57, 28, 279, -166, -48,
  148, -80, -194, -78, -53, 151, 19, 0, 102, -205, -99, 73, -31]

theorem fractionalNearFrameSubtreeG3R0164_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0164Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0164Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0164Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0164_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0164LowerBoundTable : List ℤ :=
  [-3, 2, 131, 82, -51, 128, 36, 222, 173, -283, 422, 232, 258, 501, -215,
  389, 515, -45, 302, 53, 55, 39, 10, 10, 332]

def fractionalNearFrameSubtreeG3R0164LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0164Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0164LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
