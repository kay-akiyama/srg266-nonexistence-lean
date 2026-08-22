import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0224`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0224Mask : ℕ := 2488773178200676

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0224Witness : Array ℤ :=
  #[-19, 101, 76, 101, 146, -91, 4, -30, -88, 77, 56, -100, 1, -25, -80, 0,
  -28, -55, 29, -7, -43, -25, -15, -11, 3, -3, 4, 27, 72, 89, -48, -10, -12,
  65, 72, -10, 7, -6, 16, 5, -52, 26, 7, 10, 11, 18, -12, -33, 22, 19, -1,
  15, -32, -114, 63, 45, -50, 88, 20, 50, -27, 0, -44, -37, -20, -11, 0,
  103, -44, 28, 53, 66, 5, 29, 73, -48, -40, 54, 77, -62, 0, -29, 59, 112,
  48, 64, 62, -17, -17, 14, -59, 75, 95, -20, -41, 50, 19, -79, -50, -3,
  -49, -152, -4, -2, -43, 8, 46, 7, -14, 122, 5, 11, 42, -32, 31, -71, -58,
  25, -93, 10, 40, 57, 22, -87, -13, -29, -11, 45, 32, 10, -26, -29, -51,
  -56, 63, 133, 89, -9, 44, -35, 22, -26, -57, 66, -10, -27, -48, -18, -79,
  -13, 113, -9, 9, -85, 37, 27, 9, 3, -16, -53, -11, -2, 98, 27, 42, 50, 89,
  -14]

theorem fractionalNearFrameSubtreeG2R0224_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0224Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0224Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0224Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0224_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0224LowerBoundTable : List ℤ :=
  [4, 25, 171, 2, 99, -118, 43, 3, 32, -42, 11, 563, -41, 195, 271, 207,
  161, 105, -21, 102, 146, 36, 310, 2, 86]

def fractionalNearFrameSubtreeG2R0224LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0224Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0224LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
