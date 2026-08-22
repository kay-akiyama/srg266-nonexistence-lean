import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0120`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0120Mask : ℕ := 1314549804011601

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0120Witness : Array ℤ :=
  #[11, 28, -57, -46, 33, -141, 193, 25, 143, 114, 106, 111, 0, -49, -120,
  -126, -116, -118, -23, -20, 46, -16, 31, -9, 44, -2, 42, 35, 26, 16, -99,
  -32, 78, -34, 100, 62, -59, -1, -14, -64, 0, 0, -33, -45, 16, -79, -92,
  -72, 39, -102, -8, 25, 28, 36, -41, 28, 92, -46, -59, -21, -47, 2, -66,
  -24, 12, -31, 22, -28, 31, 35, 14, 101, -55, 0, 43, -23, -84, -62, 86,
  -118, -28, -5, 47, 30, 67, 100, -40, 17, -32, 5, 29, -86, -63, -6, -19,
  -52, 5, 41, 92, 57, 4, 4, -25, 23, 2, -2, 20, 56, 28, 48, 0, 84, -109,
  -41, -1, 95, 11, -34, 55, -44, -23, -10, -28, 0, 10, 30, 24, 29, -51, 34,
  -84, 93, -82, 119, 23, -17, 2, 97, 54, 78, 55, 19, -80, 2, 100, 51, 164,
  -68, 113, 31, 26, -93, 28, 41, 48, -55, -99, -23, -12, 67, 38, 42, 53,
  -75, 40, -97, 51, -34]

theorem fractionalNearFrameSubtreeG2R0120_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0120Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0120Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0120Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0120_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0120LowerBoundTable : List ℤ :=
  [-34, 200, -118, 85, -24, 2, 65, 88, -4, 258, 238, 10, 100, 31, 51, 8,
  -256, 34, 139, 116, -11, 10, 10, 10, 306]

def fractionalNearFrameSubtreeG2R0120LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0120Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0120LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
