import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0174`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0174Mask : ℕ := 1384849696559320

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0174Witness : Array ℤ :=
  #[134, -25, 18, -6, -45, 77, 29, 4, -18, -63, 9, 34, -50, -38, 125, -92,
  3, -29, 43, 40, 19, 17, -8, -53, -11, 14, -106, -15, 56, 181, 78, -6, -31,
  -98, 5, -63, -59, -151, -7, -67, -142, -112, -78, -83, -178, 27, -57, 95,
  165, 0, -84, -69, 124, 89, -29, 98, -65, 49, 12, 78, 0, -47, 66, 20, -139,
  -6, 29, -11, -11, 75, -99, -1, -32, -100, -12, -99, 159, -186, 5, 15, -8,
  50, 0, 39, 39, -21, -35, 45, -127, -24, -79, 42, 54, 36, 5, 54, 58, 54,
  -49, -49, -12, 17, 25, 41, 65, 25, 13, 59, -128, -113, -88, -52, -3, -20,
  -31, 52, 116, 128, -156, -142, 27, 22, 8, 1, 28, -1, -16, -92, -20, -11,
  -134, 120, 92, -38, -7, -24, 183, -30, 23, 54, -115, 61, 95, -13, 80, 105,
  -60, 132, 97, 23, -135, -127, -83, -97, -58, -38, 57, 62, 63, 0, 9, 4,
  -35, -59, 9, -90, 70, 21]

theorem fractionalNearFrameSubtreeG2R0174_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0174Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0174Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0174Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0174_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0174LowerBoundTable : List ℤ :=
  [-172, 3, -111, -62, -27, 2, 2, 2, -96, 118, 10, -300, -125, 145, 54, 77,
  -546, -156, 93, 240, -68, -232, 82, 162, 107]

def fractionalNearFrameSubtreeG2R0174LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0174Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0174LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
