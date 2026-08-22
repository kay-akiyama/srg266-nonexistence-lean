import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0533`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0533Mask : ℕ := 6794668831134225

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0533Witness : Array ℤ :=
  #[-144, -89, -106, -71, -109, 0, -74, 50, 0, 82, 165, 135, -22, -17, 30,
  3, 48, 82, -106, -92, -33, -69, -39, 118, 3, 13, 88, -29, 59, 122, -71,
  92, -4, -28, 3, 9, 67, 56, -67, -60, 87, -2, 13, 33, -108, 39, 106, -50,
  105, 73, -22, 5, 19, -49, -5, 60, 76, 42, -15, 44, 80, 15, -47, 55, 17, 1,
  31, -35, 20, 16, -69, 10, -14, -30, -6, 5, 36, 41, 42, -92, -77, 26, -56,
  -34, -28, -33, 62, -2, 69, 93, 10, 35, -79, 0, -61, 3, -32, -24, 16, -16,
  49, 73, -50, -6, -8, -143, 33, 10, 176, -110, -104, -90, -30, 178, -35,
  -83, 67, -6, -42, 0, 72, -33, 93, 3, -22, -1, 59, 9, 8, -74, 30, 79, -72,
  55, 99, 105, 26, 3, 151, -41, -24, -18, 0, -142, 30, 82, -28, 12, -32,
  112, 196, 81, 49, 4, 14, -3, 21, -44, -41, 14, 79, 45, -2, -57, 13, -12,
  71, 14]

theorem fractionalNearFrameSubtreeG2R0533_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0533Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0533Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0533Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0533_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0533LowerBoundTable : List ℤ :=
  [33, 138, 3, 2, 126, 186, 1, 80, 53, 445, 129, 433, 141, 117, 74, 133,
  348, -121, -266, 153, 263, 209, 205, -65, -82]

def fractionalNearFrameSubtreeG2R0533LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0533Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0533LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
