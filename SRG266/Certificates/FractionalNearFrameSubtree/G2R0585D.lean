import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0585`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0585Mask : ℕ := 6850808605020528

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0585Witness : Array ℤ :=
  #[-51, -131, -122, 69, -18, -152, 246, 37, -138, 92, 61, -143, 283, 117,
  81, -228, -224, 31, -30, 134, -44, 587, 209, 178, 56, 118, -164, 193, -8,
  104, 254, 353, -246, -338, -140, 194, 329, -133, -227, -250, 89, 385, 71,
  0, 565, 36, 153, -305, 71, -11, 213, -30, 204, -52, -338, 254, 145, 116,
  201, -378, -170, 293, 305, -56, -72, 53, -281, 580, 105, -392, 87, 50, 93,
  4, 69, -75, 49, -630, 131, -193, 48, 200, -217, 71, 156, -318, 205, 416,
  -9, 100, -84, 17, 113, -41, -249, 118, -128, -311, -196, -122, -73, -390,
  -32, 84, -277, 258, 278, 128, 383, 433, 689, 406, 357, -335, 197, -48,
  -171, -52, -157, -140, -6, 403, 189, 226, 462, -464, 0, 99, 340, -244,
  -244, -87, 79, -21, 132, 0, -215, -334, 602, 200, 220, -141, -64, 32,
  -148, -237, 1, 150, -98, -298, -42, -115, 179, -89, 186, -44, 49, 16, 217,
  -34, 128, 111, -246, -253, 0, 106, -296, -415]

theorem fractionalNearFrameSubtreeG2R0585_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0585Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0585Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0585Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0585_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0585LowerBoundTable : List ℤ :=
  [-11, 111, 2, 64, 3, 72, 587, 860, 2, 177, 1163, 1996, 864, 246, 610, 14,
  638, -104, 153, 1038, 188, -592, -291, -256, 45]

def fractionalNearFrameSubtreeG2R0585LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0585Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0585LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
