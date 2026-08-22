import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0192`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0192Mask : ℕ := 1868729156600914

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0192Witness : Array ℤ :=
  #[77, -24, 3, 0, -10, -30, -77, -84, 17, -134, 0, 65, 140, 59, -19, -29,
  -13, 3, 27, 7, 11, -6, 17, 5, -13, -101, 14, -56, -29, 48, -3, 16, 139,
  -102, -24, -9, -13, -41, 13, 23, -4, 62, 4, -146, -67, -20, -48, 1, -17,
  -65, 44, 98, 62, 21, -35, -86, 41, 57, 53, -56, -39, 15, -13, 90, 24, 38,
  -47, 91, -9, -88, 66, 46, -54, 42, 44, 8, -73, -97, -31, 12, 52, 74, 19,
  18, -1, -28, -40, 4, 21, 60, -24, 39, 15, -1, 60, 17, 33, -17, -38, 38,
  71, -22, -2, 50, 50, 54, -29, 7, 82, -79, -50, 11, -8, 54, 36, 27, 38, -1,
  80, -55, 54, -21, -18, -70, 19, -91, 1, -11, -17, -69, -70, 1, 6, -14, 52,
  88, 83, 61, 43, -69, 37, 108, 55, 49, 61, 0, 72, 77, -43, -80, 87, 48, 48,
  -47, -94, -79, -75, 44, 0, 31, 21, -43, 2, 29, -70, -26, 9, 29]

theorem fractionalNearFrameSubtreeG2R0192_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0192Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0192Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0192Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0192_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0192LowerBoundTable : List ℤ :=
  [-44, 48, 10, 4, 49, 2, 2, 50, 1, 89, 82, 163, 241, 298, 190, -3, -169,
  236, 178, -216, 228, -8, 131, 210, 43]

def fractionalNearFrameSubtreeG2R0192LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0192Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0192LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
