import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0449`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0449Mask : ℕ := 5793158887019170

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0449Witness : Array ℤ :=
  #[-185, 1, 154, 99, 149, 19, -277, -32, 123, 17, -140, -125, -116, 108,
  110, 336, 123, 159, -45, -25, -125, -243, 199, -89, 0, 198, -26, 201, 53,
  -365, -54, 8, 215, -11, 33, 61, 178, -84, 99, -252, -25, 43, 83, 59, 229,
  234, -26, -35, -155, 193, -37, -109, -121, -78, 35, 150, 61, -127, 23,
  135, 164, -34, -53, 209, 333, 170, 148, -154, 177, 151, -25, -114, 79, 73,
  275, 42, -6, 190, -58, -94, 65, 69, 17, -31, -174, 206, -11, -96, 78, 105,
  68, 147, -148, 212, -69, -155, -40, 15, -82, 68, 111, 108, 208, -184, -88,
  -216, -297, -399, 45, 110, 181, -56, 244, 326, 222, -18, 32, -161, 72,
  -127, -71, -105, -12, 37, -43, 196, 75, -31, -8, 146, 326, 154, -108, -48,
  -237, 449, 381, 58, -45, 26, -104, -18, -90, 90, -85, -43, 14, 151, -182,
  221, 308, 47, -127, 63, -92, 347, 221, -121, 29, 188, 248, 81, -122, 6,
  -183, -33, 382, 50]

theorem fractionalNearFrameSubtreeG2R0449_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0449Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0449Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0449Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0449_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0449LowerBoundTable : List ℤ :=
  [214, 371, 710, 591, 238, 32, 1, 122, 413, 724, 193, 936, 1159, -219, 491,
  10, 1161, 75, -88, 1034, 936, 996, 536, 55, -275]

def fractionalNearFrameSubtreeG2R0449LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0449Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0449LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
