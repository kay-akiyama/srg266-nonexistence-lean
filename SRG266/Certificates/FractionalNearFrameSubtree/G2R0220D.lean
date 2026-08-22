import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0220`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0220Mask : ℕ := 2479007528288466

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0220Witness : Array ℤ :=
  #[46, -117, -11, 52, 60, -70, 93, 71, 36, 28, 148, 78, -56, -6, -51, 125,
  55, 138, 0, -47, 103, -31, 18, 58, 87, 0, -84, -39, -80, 75, -10, -19, 69,
  -34, -34, 127, -18, -15, -18, 29, -116, -66, 47, 75, 86, -12, 36, -68,
  182, -116, 65, 58, -40, -122, -46, 48, 113, -155, 129, -32, 110, -4, 94,
  -9, 200, 19, -5, 183, -16, 136, 51, 56, -8, -43, 109, 48, -306, -168, 145,
  -65, 5, 17, -63, -44, -1, 3, 113, -92, 133, 7, -83, -55, -34, -22, -15,
  47, 13, -70, 257, 85, 125, 145, 65, -134, 68, -101, -42, -108, 61, 25,
  -72, 89, 103, -11, -85, 85, -152, 126, 269, -56, 56, -210, -221, -106,
  -68, 173, -70, 185, -2, 74, 75, -23, -9, 5, -140, 48, 75, -8, 0, -103,
  200, -123, -88, -64, -92, -20, -37, 49, 39, 37, 153, -109, 28, 143, 120,
  12, -21, 84, -43, -65, -127, 74, 200, -119, 130, 0, 165, 50]

theorem fractionalNearFrameSubtreeG2R0220_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0220Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0220Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0220Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0220_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0220LowerBoundTable : List ℤ :=
  [11, 15, 83, 172, 72, 113, 149, 3, 183, 540, 608, 11, -103, -256, 141,
  -78, 349, 362, 850, 268, -25, 871, 604, 431, 10]

def fractionalNearFrameSubtreeG2R0220LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0220Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0220LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
